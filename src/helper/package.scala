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
}
