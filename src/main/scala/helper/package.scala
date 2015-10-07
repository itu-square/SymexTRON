import scala.language.higherKinds

import scala.annotation.elidable
import scala.annotation.elidable.ASSERTION
import monocle.Getter

import scalaz.{Monoid, Monad}

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
          ms ++ ms.map(transget).flatten
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
}
