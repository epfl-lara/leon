import scala.collection.immutable.Set

object VCs {
  // could solve this one in a little more than 2 minutes on my desktop machine
  def thePiskacLemma(s: Set[Int], a: Set[Int], b: Set[Int], c: Set[Int], d: Set[Int], e: Set[Int], f: Set[Int]) : Boolean = {
    require(
        (s == a ++ b ++ c)
     && (s == d ++ e ++ f)
     && (a.max < b.min)
     && (b.max < c.min)
     && (d.max < e.min)
     && (e.max < f.min)
    )
     (((a subsetOf d) || (d subsetOf a))
   && ((c subsetOf f) || (f subsetOf c)))
  } ensuring(_ == true)

  // never solved this one.
  def paperBSTFind_V(c: Set[Int], l: Set[Int], r: Set[Int], v: Int, range1: Set[Int], range2: Set[Int], range3: Set[Int]) : Boolean = {
    require(
         (c == l ++ Set(v) ++ r)
      && (l.max < v)
      && (v < r.min)
      && (range1 ++ range2 ++ range3 == c)
      && (range1.max < range2.min)
      && (range2.min < range3.max)
      && (range1.size == l.size)
      && (range2.size == 1)
      && (range3.size == c.size - l.size - 1)
      // The following lines are an application of the Piskac Lemma
      // && ((l subsetOf range1) || (range1 subsetOf l))
      // && ((r subsetOf range3) || (range3 subsetOf r))
    )
      Set(v) == range2
      // v == range2.min // this should be equivalent, right?
  } ensuring(_ == true)
}
