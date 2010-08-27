import scala.collection.immutable.Set

object CADE07 {
  def vc1(listContent: Set[Int]) : Boolean = {
    (listContent.size == 0) == (listContent == Set.empty[Int])
  } ensuring(_ == true)

  def vc2(x: Int, listContent: Set[Int]) : Set[Int] = {
    require(!listContent.contains(x))
    listContent ++ Set(x)
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

  def vc2b(listRoot: Int, list: Set[Int], x: Int, listContent: Set[Int], objectAlloc: Set[Int], objct: Set[Int]) : Set[Int] = {
    require(
      list.contains(listRoot)
   && listContent.subsetOf(objectAlloc)
   && objct.contains(x)
   && objectAlloc.contains(x))

    listContent ++ Set(x)
  } ensuring(_.size == listContent.size + 1)

  def vc3(x: Int, listContent: Set[Int]) : Set[Int] = {
    listContent ++ Set(x)
  } ensuring(_.size <= listContent.size + 1)

  def vc3a(x: Int, a: Int, b: Int, alloc: Set[Int], listContent: Set[Int]) : Set[Int] = {
    require(
      listContent.subsetOf(alloc)
   && alloc.contains(a)
   && alloc.contains(b)
    )
    listContent ++ Set(x)
  } ensuring(_.size <= listContent.size + 1)

  def vc3b(x: Int, a: Int, b: Int, alloc: Set[Int], listContent: Set[Int]) : Set[Int] = {
    require(
      listContent.subsetOf(alloc)
   && alloc.contains(a)
   && alloc.contains(b)
    )
    listContent ++ Set(x)
  } ensuring(_.size == listContent.size + 1)

  def vc4(content: Set[Int], alloc: Set[Int], x1: Int, x2: Int, x3: Int) : Set[Int] = {
    require(
      content.subsetOf(alloc)
   && !alloc.contains(x1)
   && !(alloc ++ Set(x1)).contains(x2)
   && !(alloc ++ Set(x1, x2)).contains(x3)
    )
    content ++ Set(x1, x2, x3)
  } ensuring(_.size == content.size + 3)

  def vc4b(content: Set[Int], alloc: Set[Int], x1: Int, x2: Int, x3: Int) : Set[Int] = {
    require(
      content.subsetOf(alloc)
   && !alloc.contains(x1)
   && !alloc.contains(x2)
   && !(alloc ++ Set(x1, x2)).contains(x3)
    )
    content ++ Set(x1, x2, x3)
  } ensuring(_.size == content.size + 3)

  def vc5(content: Set[Int], alloc0: Set[Int], x1: Int, alloc1: Set[Int], x2: Int, alloc2: Set[Int], x3: Int) : Set[Int] = {
    require(
      content.subsetOf(alloc0)
   && !alloc0.contains(x1)
   && (alloc0 ++ Set(x1)).subsetOf(alloc1)
   && !alloc1.contains(x2)
   && (alloc1 ++ Set(x2)).subsetOf(alloc2)
   && !alloc2.contains(x3)
    )
    content ++ Set(x1, x2, x3)
  } ensuring(_.size == content.size + 3)

  def vc5b(content: Set[Int], alloc0: Set[Int], x1: Int, alloc1: Set[Int], x2: Int, alloc2: Set[Int], x3: Int) : Set[Int] = {
    require(
      content.subsetOf(alloc0)
   && (alloc0 ++ Set(x1)).subsetOf(alloc1)
   && !alloc1.contains(x2)
   && (alloc1 ++ Set(x2)).subsetOf(alloc2)
   && !alloc2.contains(x3)
    )
    content ++ Set(x1, x2, x3)
  } ensuring(_.size == content.size + 3)

  def vc6(x: Int, c: Set[Int], c1: Set[Int], alloc0: Set[Int], alloc1: Set[Int], alloc2: Set[Int]) : Set[Int] = {
    require(
      c.contains(x)
   && c1 == c -- Set(x)
   && (alloc1 -- alloc0).size <= 1
   && (alloc2 -- alloc1).size <= c1.size
    )

    alloc2 -- alloc0
  } ensuring(_.size <= c.size)
}
