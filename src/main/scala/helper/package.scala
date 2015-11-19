import scala.language.higherKinds

import scala.annotation.elidable
import scala.annotation.elidable.ASSERTION
import monocle.Getter

import scalaz.Leibniz.===
import scalaz.{Unapply, Functor, Applicative, Monoid, Monad}
import scalaz.stream.Process
import scala.concurrent.stm._
import scalaz.concurrent.Task
import scalaz.\/
import scalaz.stream.Process

sealed trait BlackHole
case class HoleError() extends Error

package object helper {
  type StringE[B] = String \/ B
  type TProcess[A] = Process[Task, A]

  implicit class MultiMap[K, V](m : Map[K, Set[V]]) {
    def adjust[B1 >: Set[V]](key: K)(f : B1 => B1) = m updated (key, f (m getOrElse(key, Set())))
    def merge: Option[Map[K, V]] = m.foldLeft(Option(Map[K,V]())){
      (res, kv) =>
        for (r <- res;
             if kv._2.size == 1
        ) yield r + (kv._1 -> kv._2.head)
    }
  }

  implicit class TransitiveClosure[S](m: Map[S, Set[S]]) {
    def trans(): Map[S, Set[S]] = {
      def transget(s : S, seen : Set[S]) : Set[S] = {
        if (m.contains(s)) {
          val ms = m(s)
          ms ++ ms.flatMap[S,Set[S]](ss => if(!seen.contains(ss))
                                    transget(ss, seen ++ ms) else Set())
        }
        else Set()
      }
      m.keys.map(k => k -> transget(k, Set[S]())).toMap
    }
  }

  implicit class TransitiveGetter[S,M[_]](g: Getter[S, M[S]]) {
    def get_*(s : S)(implicit m: Monad[M]): M[S] = m.bind(g.get(s))(g.get_*)
  }

  implicit class RichIterable[A](it : Iterable[A]) {
    def single: Option[A] = {
      val iter = it.iterator
      if (iter.hasNext) {
        val r = iter.next()
        if (iter.hasNext) {
          None
        } else Some(r)
      } else None
    }
  }

  /**
   * An expression that fails if ever reached
   * @return no value, since it will always fail if called
   */
  @elidable(ASSERTION)
  def impossible: Nothing = throw new AssertionError("Impossible case reached")


  def hole[T]: T = throw new HoleError()
  def blackHole(hole : BlackHole) : Nothing = throw new HoleError()

  //TODO Implement these and use instead of List

  implicit class SetExtensions[A](s : Set[A]) {
    def sequenceU(implicit G: Unapply[Applicative, A]): G.M[Set[G.A]] = {
      s.traverseU(identity)
    }

    def traverseU[GB](f : A => GB)(implicit G: Unapply[Applicative, GB]): G.M[Set[G.A]] = {
      s.foldLeft(G.TC.pure(Set[G.A]()))((ss : G.M[Set[G.A]], el : A) =>
         G.TC.lift2[Set[G.A], G.A, Set[G.A]](_ + _)(ss, G.apply(f(el))))
    }
  }

  implicit def processMonad[F[_]]: Monad[({ type l[a] = Process[F, a] })#l] = new Monad[({ type l[a] = Process[F, a] })#l] {
    def point[A](a: => A): Process[F, A] = Process.emit(a)
    def bind[A, B](fa : Process[F, A])(f : A => Process[F, B]): Process[F, B] = fa.flatMap(f)
  }

  val pmn = helper.processMonad[Nothing]
  val pmt = helper.processMonad[Task]


  implicit class UnFunction1[A,B,C](f : (A, B) => C) {
    def un(b : B)(a : A): C = f (a, b)
  }

  implicit class UnFunction2[A,B,C,D](f : (A, B, C) => D) {
    def un(b : B, c : C)(a : A): D = f (a, b, c)
  }

  implicit class UnFunction3[A,B,C,D,E](f : (A, B, C, D) => E) {
    def un(b : B, c : C, d : D)(a : A): E = f(a, b, c, d)
  }

  implicit class TMapExtensions[A,B](m : TMap[A,B]) {
    def updateValue(k : A, f : B => B) = atomic { implicit txn =>
      val oldVr = m.get(k)
      oldVr.foreach(oldV => m.update(k, f(oldV)))
    }
  }
}
