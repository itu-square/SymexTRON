import scala.collection.immutable.Nil
import scala.language.higherKinds

import scala.annotation.elidable
import scala.annotation.elidable.ASSERTION
import monocle.Getter

import scalaz.Leibniz.===
import scalaz._
import scalaz.stream.Process
import scala.concurrent.stm._
import scalaz.concurrent.Task
import scalaz.stream.Process


package object helper {
  type StringE[B] = String \/ B
  type TProcess[A] = Process[Task, A]

  implicit class RichProcess[F[_], A](p : Process[F, A]) {
    def withFilter(f: A => Boolean) = p.filter(f)
  }

  implicit class RichDisjunction[A, B](d : A \/ B) {
    def withFilter(f : B => Boolean)(implicit monoid: Monoid[A]) = d.filter(f)(monoid)
  }

  implicit class RichMap[K, V](m : Map[K, V]) {
    def mapValuesWithKeys[V2](f : (K, V) => V2): Map[K, V2] =
      m map { case (k, v) => (k, f(k, v)) }
  }

  implicit class MultiMap[K, V](m : Map[K, Set[V]]) {
    def adjust[B1 >: Set[V]](key: K)(f : B1 => B1) = m updated (key, f (m getOrElse(key, Set())))
    def merge: Option[Map[K, V]] = m.foldLeft(Option(Map[K,V]())){
      (res, kv) =>
        for (r <- res
             if kv._2.size == 1) yield r + (kv._1 -> kv._2.head)
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
 *
   * @return no value, since it will always fail if called
   */
  @elidable(ASSERTION)
  def impossible: Nothing = throw new AssertionError("Impossible case reached")


  def hole[T]: T = throw new HoleError()
  def blackHole(hole : BlackHole) : Nothing = throw new HoleError()

  implicit class SetExtensions[A](sa : Set[A]) {
    def sequenceU(implicit G: Unapply[Applicative, A]): G.M[Set[G.A]] = {
      sa.traverseU(identity)
    }

    def traverseU[GB](f : A => GB)(implicit G: Unapply[Applicative, GB]): G.M[Set[G.A]] = {
      sa.foldLeft(G.TC.pure(Set[G.A]()))((ss : G.M[Set[G.A]], el : A) =>
         G.TC.lift2[Set[G.A], G.A, Set[G.A]](_ + _)(ss, G.apply(f(el))))
    }

    def pairings[B](sb: Set[B]): Set[(Set[(A, B)], Set[(A,B)])] = sa.foldLeft(Set[(Set[(A,B)], Set[A], Set[B])]((Set(), Set(), sb))) { (st, a) =>
        st.flatMap { case (assignments, unassigned, rsb) =>
          rsb.map { b => (assignments + ((a, b)), unassigned, rsb - b) } + ((assignments, unassigned + a, rsb))
        }
    } map { case (assignments, unassigneda, unassignedb) => (assignments, for (ua <- unassigneda; ub <- unassignedb) yield (ua, ub)) }
  }

  def processMonad[F[_]]: Monad[({ type l[a] = Process[F, a] })#l] = new Monad[({ type l[a] = Process[F, a] })#l] {
    def point[A](a: => A): Process[F, A] = Process.emit(a)
    def bind[A, B](fa : Process[F, A])(f : A => Process[F, B]): Process[F, B] = fa.flatMap(f)
  }

  implicit val pmn = helper.processMonad[Nothing]
  implicit val pmt = helper.processMonad[Task]


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

  implicit class InterleavedProcess[F[_],O](p: Process[F,O]) {
    val interleaved: Interleaved[F, O] = Interleaved(p)
  }

  implicit class LiftMatch[A](a : A) {
    def liftMatch[B,M[_]](f : PartialFunction[A,B])(implicit monadPlus: MonadPlus[M]): M[B] =
      if (f.isDefinedAt(a)) monadPlus.point(f(a)) else monadPlus.empty
  }
  implicit class ListNormalizeOps[A](l : List[A]) {
    def normalizeMonoidal(implicit monoid: Monoid[A]): A = l match {
      case Nil => monoid.zero
      case x :: xs if x == monoid.zero => xs.normalizeMonoidal
      case x :: xs => xs match {
        case Nil => x
        case _ => monoid.append(x, xs.normalizeMonoidal)
      }
    }
  }
}

sealed trait BlackHole
case class HoleError() extends Error

case class Interleaved[+F[_],+O](toProcess: Process[F, O]) {
  def map[O2](f : O => O2) = Interleaved(toProcess.map(f))

  def flatMap[F2[x] >: F[x], O2](f: O => Interleaved[F2, O2])
  : Interleaved[F2, O2] = Interleaved {
    toProcess.fold(Process.halt : Process[F2, O2])((ps, o) =>
      ps.tee((f(o).toProcess))(helper.teePlus.interleaveAll)
    ).flatMap(identity)
  }
}

