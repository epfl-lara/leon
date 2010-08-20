import scala.collection.immutable.Set

object CADE07 {
  def vc1(listContent: Set[Int]) : Boolean = {
    (listContent.size == 0) == (listContent == Set.empty[Int])
  } ensuring(_ == true)

  def vc2(x: Int, listContent: Set[Int]) : Set[Int] = {
    require(!listContent.contains(x))
    listContent ++ Set(x)
  } ensuring(_.size == listContent.size + 1)

  def vc2r(x: Set[Int], listContent: Set[Int]) : Set[Int] = {
    require(x.size == 1 && !x.subsetOf(listContent))
    listContent ++ x
  } ensuring(_.size == listContent.size + 1)

  def vc2a(listRoot: Int, list: Set[Int], x: Int, listContent: Set[Int], objectAlloc: Set[Int], objct: Set[Int]) : Set[Int] = {
    require(
      list.contains(listRoot)
   && !listContent.contains(x)
   && listContent.subsetOf(objectAlloc)
   && objct.contains(x)
   && objectAlloc.contains(x))

    listContent ++ Set(x)
  } ensuring(_.size == listContent.size + 1)

  def vc2ar(listRoot: Set[Int], list: Set[Int], x: Set[Int], listContent: Set[Int], objectAlloc: Set[Int], objct: Set[Int]) : Set[Int] = {
    require(
      listRoot.size == 1
   && listRoot.subsetOf(list)
   && x.size == 1
   && !x.subsetOf(listContent)
   && listContent.subsetOf(objectAlloc)
   && x.subsetOf(objct)
   && x.subsetOf(objectAlloc))

    listContent ++ x
  } ensuring(_.size == listContent.size + 1)

  def vc2b(listRoot: Int, list: Set[Int], x: Int, listContent: Set[Int], objectAlloc: Set[Int], objct: Set[Int]) : Set[Int] = {
    require(
      list.contains(listRoot)
   && listContent.subsetOf(objectAlloc)
   && objct.contains(x)
   && objectAlloc.contains(x))

    listContent ++ Set(x)
  } ensuring(_.size == listContent.size + 1)

  def vc2br(listRoot: Set[Int], list: Set[Int], x: Set[Int], listContent: Set[Int], objectAlloc: Set[Int], objct: Set[Int]) : Set[Int] = {
    require(
      listRoot.size == 1
   && listRoot.subsetOf(list)
   && x.size == 1
   && listContent.subsetOf(objectAlloc)
   && x.subsetOf(objct)
   && x.subsetOf(objectAlloc)
    )

    listContent ++ x
  } ensuring(_.size == listContent.size + 1)

  def vc3(x: Int, listContent: Set[Int]) : Set[Int] = {
    listContent ++ Set(x)
  } ensuring(_.size <= listContent.size + 1)

  def vc3r(x: Set[Int], listContent: Set[Int]) : Set[Int] = {
    require(x.size == 1)
    listContent ++ x
  } ensuring(_.size <= listContent.size + 1)

  def vc6(x: Int, c: Set[Int], c1: Set[Int], alloc0: Set[Int], alloc1: Set[Int], alloc2: Set[Int]) : Set[Int] = {
    require(
      c.contains(x)
   && c1 == c -- Set(x)
   && (alloc1 -- alloc0).size <= 1
   && (alloc2 -- alloc1).size <= c1.size
    )

    alloc2 -- alloc0
  } ensuring(_.size <= c.size)

  def vc6r(x: Set[Int], c: Set[Int], c1: Set[Int], alloc0: Set[Int], alloc1: Set[Int], alloc2: Set[Int]) : Set[Int] = {
    require(
      x.size == 1
   && x.subsetOf(c)
   && c1 == c -- x
   && (alloc1 -- alloc0).size <= 1
   && (alloc2 -- alloc1).size <= c1.size
    )

    alloc2 -- alloc0
  } ensuring(_.size <= c.size)
}
