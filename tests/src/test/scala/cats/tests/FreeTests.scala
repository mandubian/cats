package cats
package tests

import std.all._
import data._
import free._
import Free.Trampoline

// the things we assert here are not so much important, what is
// important is that this stuff compiles at all.
class FreeTests extends CatsSuite {

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
    assert(testTime2("rgtBind 1000000")(rgtBind(1000000)(gen _).run) == 1000000)
  }
}
