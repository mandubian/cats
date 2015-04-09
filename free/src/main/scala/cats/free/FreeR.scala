package cats
package freer

import scala.annotation.tailrec

sealed abstract class FreeView[S[_], A]

object FreeView {
  case class Pure[S[_], A](a: A) extends FreeView[S, A]
  case class Impure[S[_], A](a: S[FreeR[S, A]]) extends FreeView[S, A]
}


import FreeR._

sealed abstract class FreeR[S[_], A] {
  import Op._
  import Val._
  import FreeView._

  def map[B](f: A => B) = FreeR.map(this)(f)
  def flatMap[B](f: A => FreeR[S, B]) = FreeR.bind(this)(f)

  def toView(implicit S: Functor[S]): FreeView[S, A] = FreeR.toView(this)

  final def resume(implicit S: Functor[S]): (Either[S[FreeR[S, A]], A]) = FreeR.toView(this) match {
    case Pure(a) => Right(reify[A](a))
    case Impure(fm) => Left(fm)
  }

  /**
   * Runs to completion, using a function that extracts the resumption
   * from its suspension functor.
   */
  final def go(f: S[FreeR[S, A]] => FreeR[S, A])(implicit S: Functor[S]): A = {
    @tailrec def loop(t: FreeR[S, A]): A =
      t.resume match {
        case Left(s) => loop(f(s))
        case Right(r) => r
      }
    loop(this)
  }


  def run(implicit S: Comonad[S]): A = go(S.extract)

  /**
   * Runs to completion, using a function that maps the resumption
   * from `S` to a monad `M`.
   */
  final def runM[M[_]](f: S[FreeR[S, A]] => M[FreeR[S, A]])(implicit S: Functor[S], M: Monad[M]): M[A] = {
    def runM2(t: FreeR[S, A]): M[A] = t.resume match {
      case Left(s) => Monad[M].flatMap(f(s))(runM2)
      case Right(r) => Monad[M].pure(r)
    }
    runM2(this)
  }

  /**
   * Catamorphism for `Free`.
   *
   * Runs to completion, mapping the suspension with the given transformation at each step and
   * accumulating into the monad `M`.
   */
  final def foldMap[M[_]](f: S ~> M)(implicit S: Functor[S], M: Monad[M]): M[A] =
    this.resume match {
      case Left(s) => Monad[M].flatMap(f(s))(_.foldMap(f))
      case Right(r) => Monad[M].pure(r)
    }

  /** Compiles your Free into another language by changing the suspension functor
   *  using the given natural transformation.
   *  Be careful if your natural transformation is effectful, effects are applied by mapSuspension
   */
  final def mapSuspension[T[_]](f: S ~> T)(implicit S: Functor[S], T: Functor[T]): FreeR[T, A] =
    this.resume match {
      case Left(s)  => fromView(Impure(f(S.map(s)(((_: FreeR[S, A]) mapSuspension f)))))
      case Right(r) => fromView(Pure(r))
    }

  final def compile[T[_]](f: S ~> T)(implicit S: Functor[S], T: Functor[T]): FreeR[T, A] = mapSuspension(f)

  final def mapFusion(implicit fs: Functor[S]): FreeR[S, A] = FreeR.mapFusion(this)
}

object FreeR {
  import FreeView._
  import Op._
  import Val._

  case class FreeR0[S[_], A](head: FreeView[S, Val]) extends FreeR[S, A]
  case class FreeR1[S[_], A](head: FreeView[S, Val], op: Op) extends FreeR[S, A]
  case class FreeRs[S[_], A](head: FreeView[S, Val], ops: Ops = Vector.empty) extends FreeR[S, A]

  implicit def FreeRMonad[S[_]] = new Monad[({ type l[A] = FreeR[S, A] })#l] {
    def pure[A](a: A): FreeR[S, A] = FreeR.pure(a)
    def flatMap[A, B](fa: FreeR[S, A])(f: A => FreeR[S, B]): FreeR[S, B] = FreeR.bind(fa)(f)
  }

  final def pure[S[_], A](a: A): FreeR[S, A] = FreeR0(Pure[S, Val](cast(a)))

  final def suspend[S[_], A](s: S[FreeR[S, A]]): FreeR[S, A] = FreeR0(Impure[S, Val](castK2[FreeR, S, A](s)))

  final def bind[S[_], A, B](free: FreeR[S, A])(f: A => FreeR[S, B]): FreeR[S, B] =
    free match {
      case FreeR0(h) => FreeR1(h, Bind(x => castK1[FreeR, S, B](f(reify[A](x)))))
      case FreeR1(h, op) => FreeRs(h, Vector(op, Bind(x => castK1[FreeR, S, B](f(reify[A](x))))))
      case FreeRs(h, t) => FreeRs(h, t :+ Bind(x => castK1[FreeR, S, B](f(reify[A](x)))))
    }

  final def map[S[_], A, B](free: FreeR[S, A])(f: A => B): FreeR[S, B] =
    free match {
      case FreeR0(h) => FreeR1(h, Map(x => f(reify[A](x))))
      case FreeR1(h, op) => FreeRs(h, Vector(op, Map(x => f(reify[A](x)))))
      case FreeRs(h, t) => FreeRs(h, t :+ Map(x => f(reify[A](x))))
    }

  /** Suspends a value within a functor lifting it to a Free */
  final def liftF[F[_], A](value: => F[A])(implicit F: Functor[F]): FreeR[F, A] =
    suspend[F, A](F.map(value)(pure _))

  final def fromView[S[_], A](h: FreeView[S, A]): FreeR[S, A] = FreeR0(castK1(h))

  @tailrec
  final def toView[S[_], A](f: FreeR[S, A])(implicit sf: Functor[S]): FreeView[S, A] = {
    f match {
      case FreeR0(h) => reifyK1[FreeView, S, A](h)

      case FreeR1(h, op) => h match {
        case Pure(x) => op match {
          case Map(fmap) => Pure(reify[A](fmap(x)))
          case Bind(bind) => toView(reifyK11[FreeR, S, A](bind(x)))
        }

        case Impure(f) =>
          Impure(
            sf.map(f){ fm =>
              fm match {
                case FreeR0(h) => FreeR1(h, op)
                case FreeR1(h, op0) => FreeRs(h, Vector(op0, op))
                case FreeRs(h, t) => FreeRs(h, t :+ op)
              }
          })
          
      }

      case FreeRs(h, t) => h match {
        case Pure(x) => t match {
          case Vector() => Pure(reify[A](x))
          case fh +: tailOps => fh match {
            case Map(fmap) => toView(FreeRs(Pure[S, Val](fmap(x)), tailOps))
            case Bind(bind) =>
              val fm = castK11[FreeR, S, Val](bind(x))
              fm match {
                case FreeR0(h) => toView(FreeRs(h, tailOps))
                case FreeR1(h, op0) => toView(FreeRs(h, op0 +: tailOps))
                case FreeRs(h, t) => toView(FreeRs(h, t ++ tailOps))
              }
          }
        }

        case Impure(f) =>
          Impure(
            sf.map(f){ fm =>
              fm match {
                case FreeR0(h) => FreeRs(h, t)
                case FreeR1(h, op0) => FreeRs(h, op0 +: t)
                case FreeRs(h, t0) => FreeRs(h, t0 ++ t)
              }
          })
      }
    }

  }

  def mapFusion[S[_], A](f: FreeR[S, A])(implicit sf: Functor[S]): FreeR[S, A] =
    f match {
      case FreeR0(_) => f

      /*h match {
        case Pure(_) => f

        case Impure(f) => FreeR0(Impure(sf.map(f){
          fm => fm match {
            case FreeR0(h) => fm
            case FreeR1(h, op0) => fm
            case FreeRs(h, t) => FreeRs(h, Ops.mapFusion(t))
          }
        }))
      }*/

      case FreeR1(_, _) => f

      /*h match {
        case Pure(_) => f

        case Impure(f) => FreeR1(Impure(sf.map(f){
          fm => fm match {
            case FreeR0(h) => fm
            case FreeR1(h, op0) => fm
            case FreeRs(h, t) => FreeRs(h, Ops.mapFusion(t))
          }
        }), op)
      }*/

      case FreeRs(h, t) => FreeRs(h, Ops.mapFusion(t))

      /*h match {
        case Pure(_) => FreeRs(h, Ops.mapFusion(t))

        case Impure(_) => FreeRs(Impure(sf.map(f){
          fm => fm match {
            case FreeR0(h) => fm
            case FreeR1(h, op0) => fm
            case FreeRs(h, t) => FreeRs(h, Ops.mapFusion(t))
          }
        }))
      }*/
    }


  type Ops = Vector[Op]

  object Ops {

    def mapFusion[S[_], A](h: Ops): Ops = {
      @tailrec
      def step(resOps: Ops, accOp: Option[Map], ops: Ops): Ops = 
        ops match {
          case Vector() => accOp match {
            case None => resOps
            case Some(op) => resOps :+ op
          }
          case op1 +: opsTail => op1 match {
            case Map(f) => 
              step(resOps, accOp match {
                case None => Some(Map(f))
                case Some(Map(g)) => Some(Map(f compose g))
              }, opsTail)

            case _ =>
              accOp match {
                case None => step(resOps :+ op1, None, opsTail)
                case Some(op2) => step(resOps :+ op1 :+ op2, None, ops)
              }
          }
        }
      step(h, None, Vector())
    }

  }

  type Val = Any

  object Val {
    // val unit: Val = cast(Unit)
    @inline def cast(x: Any): Val = x.asInstanceOf[Val]
    @inline def reify[A](x: Val): A = x.asInstanceOf[A]
    @inline def reifyK1[F[_[_], _], G[_], A](x: F[G, Val]): F[G, A] = x.asInstanceOf[F[G, A]]
    @inline def reifyK11[F[_[_], _], G[_], A](x: F[Any, Val]): F[G, A] = x.asInstanceOf[F[G, A]]
    @inline def reifyK2[F[_[_], _], G[_], A](x: G[F[G, Val]]): G[F[G, A]] = x.asInstanceOf[G[F[G, A]]]

    @inline def castK[F[_]](x: F[Any]): F[Val] = x.asInstanceOf[F[Val]]
    @inline def castK1[F[_[_], _], G[_], A](x: F[G, A]): F[G, Val] = x.asInstanceOf[F[G, Val]]
    @inline def castK11[F[_[_], _], G[_], A](x: F[Any, A]): F[G, Val] = x.asInstanceOf[F[G, Val]]
    @inline def castK2[F[_[_], _], G[_], A](x: G[F[G, A]]): G[F[G, Val]] = x.asInstanceOf[G[F[G, Val]]]
  }

  sealed trait Op
  object Op {
    case class Map(f: Val => Val) extends Op
    case class Bind[S[_]](f: Val => FreeR[S, Val]) extends Op
    // case class Apply(f: (Val, Val) => Val, left: Thunk, right: Thunk) extends Op
  }

  import cats.std.function._
  type Trampoline[A] = FreeR[Function0, A]

  object Trampoline {

    def done[A](a: A): Trampoline[A] = pure[Function0, A](a)

    def suspend[A](a: => Trampoline[A]): Trampoline[A] = fromView(Impure[Function0, A](() => a))

    def delay[A](a: => A): Trampoline[A] = suspend(done(a))

  }

  implicit class TrampolineOps[A](val tr: Trampoline[A]) {
    /** Runs a trampoline all the way to the end, tail-recursively. */
    def run: A = tr.go(_())
  }

}
