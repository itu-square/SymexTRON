import scala.language.higherKinds

import scala.annotation.elidable
import scala.annotation.elidable.ASSERTION
import monocle.Getter

import scalaz.Leibniz.===
import scalaz.{Unapply, Functor, Applicative, Monoid, Monad}
import scalaz.stream.Process

package object helper {
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
      def transget(s : S) : Set[S] = {
        if (m.contains(s)) {
          val ms = m(s)
          ms ++ ms.flatMap(transget)
        }
        else Set()
      }
      m.keys.map(k => k -> transget(k)).toMap
    }
  }

  implicit class TransitiveGetter[S,M[_]](g: Getter[S, M[S]]) {
    def get_*(s : S)(implicit m: Monad[M]): M[S] = m.bind(g.get(s))(g.get_*)
  }

  /**
   * An expression that fails if ever reached
   * @return no value, since it will always fail if called
   */
  @elidable(ASSERTION)
  def impossible: Nothing = throw new AssertionError("Impossible case reached")

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
}
