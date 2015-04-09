package cats
package tests

import std.all._

import cats.std.AllInstances
import cats.syntax.AllSyntax

import data._
import freer._
import FreeR.Trampoline
import scala.annotation.tailrec

import cats.std.function._
import FreeView._


object FreeRTools extends AllInstances with AllSyntax {

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

  //(a flatMap (b flatMap (c flatMap (...))))
  def mapalot(n: Int): Trampoline[Long] = {
    (1 to n).foldLeft(Trampoline.done(0L)){ case (acc, i) => acc map { a => a + 1 } }
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

  type Iteratee[I, A] = FreeR[({ type l[T] = Get[I, T]})#l, A]

  object Iteratee {
    def get[I]: Iteratee[I, I] =
      FreeR.suspend[({ type λ[T] = Get[I, T] })#λ, I](Get((x:I) => FreeR.pure[({ type λ[T] = Get[I, T] })#λ, I](x)))

    // implicit def functor[I] = new Functor[({ type λ[T] = I => T })#λ] {
    //   def map[A, B](fa: ({ type λ[T] = I => T })#λ[A])(f: A => B): ({ type λ[T] = I => T })#λ[B] = i => f(fa(i))
    // }

    def addGet(i: Long): Iteratee[Long, Long] = get[Long].map(_ + i)

    // def addNbad(n: Int): Iteratee[Int, Int] = (Seq.fill(n)(addGet _).foldLeft(FreeR.pure[({ type λ[T] = Int => T })#λ, Int] _){ (acc, f) => 
    //   (i:Int) => {
    //     println(s"i:$i")

    //     acc(i).flatMap(f)
    //   }
    // })(0)

    def addNbad(n: Int): Iteratee[Long, Long] = {
      //Seq.fill(n)(addGet _).foldLeft(M.point[Int](0)){ case (acc, f) => M.bind(acc)(f) }

      @tailrec def step(i: Long, it: Iteratee[Long, Long]): Iteratee[Long, Long] = {
        if(i < n) step(i+1, it.flatMap(addGet _)) else it
      }

      step(0, FreeR.pure[({ type λ[T] = Get[Long, T] })#λ, Long](0))
    }

    def feedAll[I, A](f: Iteratee[I, A])(l: List[I]): Option[A] = {
      (f.toView, l) match {
        case (p:Pure[({ type λ[T] = Get[I, T] })#λ, A], _) => Some(p.a)
        case (_, Nil) => None
        case (i:Impure[({ type λ[T] = Get[I, T] })#λ, A], h :: t) => feedAll(i.a.f(h))(t)
      }
    }

    def testQuadratic(n: Int) = feedAll (addNbad(n)) ((1 to n).map(_.toLong).toList)

  }

}

// the things we assert here are not so much important, what is
// important is that this stuff compiles at all.
class FreeRTests extends CatsSuite {
  import FreeRTools._

  test("FreeR Monoid is a list") {
    type FreeMonoid[A] = FreeR[({type λ[+α] = (A,α)})#λ, Unit]

    implicit def functor[C] = new Functor[({type λ[+α] = (C,α)})#λ] {
      def map[A, B](fa: ({type λ[+α] = (C,α)})#λ[A])(f: A => B): ({type λ[+α] = (C,α)})#λ[B] = (fa._1, f(fa._2))
    }

    object ListF {
      def cons[A](a: A): FreeMonoid[A] = FreeR.suspend[({type λ[+α] = (A,α)})#λ, Unit]((a, FreeR.pure[({type λ[+α] = (A,α)})#λ, Unit](())))
    
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

  test("FreeR Trampoline is stacksafe") {

    assert(even(List(1, 2, 3)).run == false)
    assert(even(List(1, 2, 3, 4)).run == true)
    assert(even((0 to 300000).toList).run == false)
  }

  test("FreeR should support left binds") {
    assert(testTime2("lftBindR 10000000")(lftBind(1000000)(gen _).run) == 1000000)
  }

  test("FreeR should support right binds") {
    val f = testTime2("rgtBindR build 1000000")(rgtBind(1000000)(gen _))
    val r = testTime2("rgtBindR run 1000000")(f.run)
    assert(r == 1000000)
  }

  test("FreeR should observe iteratees in non quadratic complexity") {

    var r = testTime2("iteratee test 10000")(Iteratee.testQuadratic(10000))
    assert(r == Some(50005000L))

    r = testTime2("iteratee test 20000")(Iteratee.testQuadratic(20000))
    assert(r == Some(200010000L))

    r = testTime2("iteratee test 30000")(Iteratee.testQuadratic(30000))
    assert(r == Some(450015000L))

    r = testTime2("iteratee test 40000")(Iteratee.testQuadratic(40000))
    assert(r == Some(800020000L))

    r = testTime2("iteratee test 50000")(Iteratee.testQuadratic(50000))
    assert(r == Some(1250025000L))

    r = testTime2("iteratee test 100000")(Iteratee.testQuadratic(100000))
    assert(r == Some(5000050000L))


  }

  test("FreeR should mapFusion") {
    val free = mapalot(1000000)
    val freeOpt = free.mapFusion

    var r = testTime2("map a lot 1000000")(free.run)
    assert(r == 1000000L)

    r = testTime2("map a lot FUSION 1000000")(freeOpt.run)
    assert(r == 1000000L)
  }
}


/*
    import cats.tests.FreeRTools
    import FreeRTools.ptime
    import com.quantifind.charts.Highcharts._
    import cats.std.function._

    val l = List(100000, 200000, 300000, 400000, 500000, 1000000, 2000000, 5000000)
    val p1 = l map { x => ptime(FreeRTools.Iteratee.testQuadratic(x)) }

    val lft1 = l map { x => ptime(FreeRTools.lftBind(x)(FreeRTools.gen _).run) }
    val rgt1 = l map { x => ptime(FreeRTools.rgtBind(x)(FreeRTools.gen _).run) }

    val mfs = l map { x => 
      val free = mapalot(x)
      val freeOpt = free.mapFusion
      ptime(free.run) -> ptime(freeOpt.run)
    }

    line( l zip mfs.map(_._1) )
    line( l zip mfs.map(_._2) )

*/