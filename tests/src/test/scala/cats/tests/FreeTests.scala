package cats
package tests

import std.all._
import cats.std.AllInstances
import cats.syntax.AllSyntax

import data._
import free._
import Free.Trampoline
import scala.annotation.tailrec


object FreeTools extends AllInstances with AllSyntax {

  def even[A](ns: List[A]): Trampoline[Boolean] =
    ns match {
      case Nil => Trampoline.done(true)
      case x :: xs => Trampoline.suspend(odd(xs))
    }
  def odd[A](ns: List[A]): Trampoline[Boolean] =
    ns match {
      case Nil => Trampoline.done(false)
      case x :: xs => Trampoline.suspend(even(xs))
    }

  def gen[I](i: I): Trampoline[I] = Trampoline.suspend(Trampoline.done(i))
  
  //(a flatMap (b flatMap (c flatMap (...))))
  def lftBind[S[_]](n: Int)(gen: Int => S[Int])(implicit M: Monad[S]) = {
    (1 to n).foldLeft(gen(0)){ case (acc, i) => acc flatMap { a => gen(i) } }
  }

  // (... flatMap (_ => c flatMap (_ => b flatMap (_ => a))))
  def rgtBind[S[_]](n: Int)(gen: Int => S[Int])(implicit M: Monad[S]) = {
    (1 to n).foldLeft(gen(n)){ case (acc, i) => gen(n-i) flatMap { _ => acc } }
  }

  def testTime2[A](name: String)(body: => A): A = {
    val t1 = System.currentTimeMillis()
    val r = body
    val t2 = System.currentTimeMillis()
    println( name + " " + formatSeconds( (t2 - t1) * 0.001 ) )
    r
  }

  def formatSeconds( seconds: Double ) : String = {
    val millisR    = (seconds * 1000).toInt
    val sb         = new StringBuilder( 10 )
    val secsR      = millisR / 1000
    val millis     = millisR % 1000
    val mins       = secsR / 60
    val secs       = secsR % 60
    if( mins > 0 ) {
       sb.append( mins )
       sb.append( ':' )
       if( secs < 10 ) {
          sb.append( '0' )
       }
    }
    sb.append( secs )
    sb.append( '.' )
    if( millis < 10 ) {
       sb.append( '0' )
    }
    if( millis < 100 ) {
       sb.append( '0' )
    }
    sb.append( millis )
    sb.append( 's' )
    sb.toString()
  }

  def ptime[A](f: => A): Double = {
    val t0 = System.nanoTime
    val ans = f
    (System.nanoTime-t0)*1e-9
  }

  case class Get[I, A](f: I => A)

  object Get {
    implicit def F[I] = new Functor[({ type l[T] = Get[I, T]})#l] {
      def map[A, B](a: Get[I, A])(f: A => B): Get[I, B] = Get[I, B](i => f(a.f(i)))
    }
  }

  sealed abstract class FreeView[S[_], A] 

  object FreeView {
    case class Pure[S[_], A](a: A) extends FreeView[S, A]
    case class Impure[S[_], A](a: S[Free[S, A]]) extends FreeView[S, A]
  }

  import FreeView._

  def toView[S[_]: Functor, A](free: Free[S, A]): FreeView[S, A] = free.resume match {
    case Right(a) => Pure(a)
    case Left(s) => Impure(s)
  }

  def fromView[S[_], A](v: FreeView[S, A]): Free[S, A] = v match {
    case Pure(a)    => Free.Pure(a)
    case Impure(f)  => Free.Suspend(f)
  }

  type Iteratee[I, A] = Free[({ type l[T] = Get[I, T]})#l, A]

  object Iteratee {
    def get[I] : Iteratee[I, I] = {

      type Get0[T] = ({ type l[a] = Get[I, a]})#l[T]

      fromView[Get0, I](
        Impure[Get0, I](
          Get( (i:I) => Free.Pure(i) )
        )
      )
    }

    def addGet(i: Long): Iteratee[Long, Long] = {
      get[Long] map { x => x + i }
    }

    def addNbad(n: Int): Iteratee[Long, Long] = {
      //Seq.fill(n)(addGet _).foldLeft(M.point[Int](0)){ case (acc, f) => M.bind(acc)(f) }

      @tailrec def step(i: Int, Iteratee: Iteratee[Long, Long]): Iteratee[Long, Long] = {
        if(i < n) step(i+1, Iteratee.flatMap(addGet _)) else Iteratee
      }

      step(0, Free.Pure[({ type l[T] = Get[Long, T]})#l, Long](0))
    }

    def feedAll[I, A](Iteratee: Iteratee[I, A])(l: Seq[I]): Option[A] = {
      @tailrec def step(Iteratee: Iteratee[I, A])(l: Seq[I]): Option[A] = {
        toView[({ type l[T] = Get[I, T]})#l, A](Iteratee) match {
          case t: Pure[({ type l[T] = Get[I, T]})#l, a]   => Some(t.a)
          case t: Impure[({ type l[T] = Get[I, T]})#l, a] =>
            l match {
              case Nil    => None
              case h +: l => step(t.a.f(h))(l)
            }
        }
      }

      step(Iteratee)(l)
    }

    def testQuadratic(n: Int) = feedAll (addNbad(n)) ((1 to n).map(_.toLong).toList)
  }
}

// the things we assert here are not so much important, what is
// important is that this stuff compiles at all.
class FreeTests extends CatsSuite {
  import FreeTools._

  test("Free Monoid is a list") {
    type FreeMonoid[A] = Free[({type λ[+α] = (A,α)})#λ, Unit]

    implicit def functor[C] = new Functor[({type λ[+α] = (C,α)})#λ] {
      def map[A, B](fa: ({type λ[+α] = (C,α)})#λ[A])(f: A => B): ({type λ[+α] = (C,α)})#λ[B] = (fa._1, f(fa._2))
    }

    object ListF {
      def cons[A](a: A): FreeMonoid[A] = Free.Suspend[({type λ[+α] = (A,α)})#λ, Unit]((a, Free.Pure[({type λ[+α] = (A,α)})#λ, Unit](())))
    
      def toList[A](list: FreeMonoid[A]): List[A] =
         list.resume.fold(
           { case (x, xs) => x :: toList(xs) },
           { _ => Nil })
    }

    assert(ListF.toList(ListF.cons(1)) == List(1))

    assert(ListF.toList(
      for {
        _ <- ListF.cons(1)
        _ <- ListF.cons(2)
        _ <- ListF.cons(3)
      } yield ()) == List(1, 2, 3))
  }

  test("Free Trampoline is stacksafe") {

    assert(even(List(1, 2, 3)).run == false)
    assert(even(List(1, 2, 3, 4)).run == true)
    assert(even((0 to 300000).toList).run == false)
  }

  // test("Free should support left binds") {
  //   assert(testTime2("lftBind 10000000")(lftBind(10000000)(gen _).run) == 10000000)
  // }

  test("Free should support right binds") {
    val f = testTime2("rgtBind build 1000000")(rgtBind(1000000)(gen _))
    val r = testTime2("rgtBind run 1000000")(f.run)
    assert(r == 1000000)
  }

  test("Free should observe Iteratees in non quadratic complexity") {

    var r = testTime2("Iteratee test 10000")(Iteratee.testQuadratic(10000))
    assert(r == Some(50005000L))

    r = testTime2("Iteratee test 20000")(Iteratee.testQuadratic(20000))
    assert(r == Some(200010000L))

    r = testTime2("Iteratee test 30000")(Iteratee.testQuadratic(30000))
    assert(r == Some(450015000L))

    r = testTime2("Iteratee test 40000")(Iteratee.testQuadratic(40000))
    assert(r == Some(800020000L))

    r = testTime2("Iteratee test 50000")(Iteratee.testQuadratic(50000))
    assert(r == Some(1250025000L))

    r = testTime2("Iteratee test 100000")(Iteratee.testQuadratic(100000))
    assert(r == Some(5000050000L))


  }
}

/*
    import cats.tests.FreeTools
    import FreeTools.ptime
    import com.quantifind.charts.Highcharts._

    val l = List(100000, 200000, 300000, 400000, 500000, 1000000, 2000000, 5000000)
    val p0 = l map { x => ptime(FreeTools.Iteratee.testQuadratic(x)) }
    
    val lft0 = l map { x => ptime(FreeTools.lftBind(x)(FreeTools.gen _).run) }
    val rgt0 = l map { x => ptime(FreeTools.rgtBind(x)(FreeTools.gen _).run) }

    line(l zip p0)
*/