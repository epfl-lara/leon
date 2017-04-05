package leon.utils

object MapUtils {
  def union[A, B](m1: Map[A, Seq[B]], m2: Map[A, Seq[B]]): Map[A, Seq[B]] = {
    (for(k <- (m1.keySet ++ m2.keySet).toSeq) yield {
      k -> (m1.getOrElse(k, Nil) ++ m2.getOrElse(k, Nil))
    }).toMap
  }

  def seqToMap[A, B](a: Seq[(A, B)]): Map[A, Seq[B]] = {
    a.groupBy(_._1).map { case (k, v) => k -> v.map(_._2) }
  }
}
