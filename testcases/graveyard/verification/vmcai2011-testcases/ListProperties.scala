import leon.lang._

object IntListProperties {
  sealed abstract class IntList
  case class Cons(head: Int, tail: IntList) extends IntList
  case class Nil() extends IntList

  def size(list: IntList) : Int = (list match {
    case Nil() => 0
    case Cons(_, xs) => 1 + size(xs)
  }) ensuring(_ >= 0)

  sealed abstract class IntTree
  case class Node(left: IntTree, value: Int, right: IntTree) extends IntTree
  case class Leaf() extends IntTree

  def size(tree: IntTree) : Int = (tree match {
    case Leaf() => 0
    case Node(l,_,r) => 1 + size(l) + size(r)
  }) ensuring(_ >= 0)

  def height(tree: IntTree) : Int = (tree match {
    case Leaf() => 0
    case Node(l,_,r) => {
      val hl = height(l)
      val hr = height(r)
      (if(hl > hr) hl else hr) + 1
    }
  }) ensuring(res => res >= 0 && res <= size(tree))

  def pickOne(s: Set[Int]) : Int = {
    require(s != Set.empty[Int])
    throw new Exception("Uninterpreted.")
    0
  } ensuring(s.contains(_))

  def listContent(list: IntList) : Set[Int] = (list match {
    case Nil() => Set.empty[Int]
    case Cons(x, xs) => Set(x) ++ listContent(xs)
  }) ensuring(_.size <= size(list))

  def treeContent(tree: IntTree) : Set[Int] = (tree match {
    case Leaf() => Set.empty[Int]
    case Node(l, v, r) => treeContent(l) ++ Set(v) ++ treeContent(r)
  }) ensuring(_.size <= size(tree))

  def listReverse(list: IntList, tsil: IntList) : IntList = {
    list match {
      case Nil() => tsil
      case Cons(x, xs) => listReverse(xs, Cons(x, tsil))
    }
  } ensuring(res => listContent(res) == listContent(list) ++ listContent(tsil))

  def treeMirror(tree: IntTree) : IntTree = (tree match {
    case Leaf() => Leaf()
    case Node(l, v, r) => Node(treeMirror(r), v, treeMirror(l))
  }) ensuring(res => treeContent(res) == treeContent(tree))

  def listFromSet(s: Set[Int]) : IntList = listFromSet0(s, Nil()) ensuring(res =>
      listContent(res) == s
   && size(res) == s.size
  )
  def listFromSet0(s: Set[Int], acc: IntList) : IntList = {
    require(listContent(acc) ** s == Set.empty[Int])
    if(s == Set.empty[Int]) {
      acc
    } else {
      val e = pickOne(s)
      listFromSet0(s -- Set(e), Cons(e, acc))
    }
  } ensuring(res => 
     listContent(res) == listContent(acc) ++ s
  && size(res) == size(acc) + s.size
    )

  def treeToList0(tree: IntTree, acc: IntList) : IntList = {
    tree match {
      case Leaf() => acc
      case Node(l,v,r) => l match {
        case Leaf() => treeToList0(r, Cons(v, acc))
        case Node(l2,v2,r2) => treeToList0(Node(l2, v2, Node(r2, v, r)), acc)
      }
    }
  } ensuring(listContent(_).size == treeContent(tree).size + listContent(acc).size)

  def concatReverse(l1: IntList, l2: IntList) : IntList = concatReverse0(l1, l2, Nil())
  def concatReverse0(l1: IntList, l2: IntList, acc: IntList) : IntList = {
    l1 match {
      case Nil() => l2 match {
        case Nil() => acc
        case Cons(y, ys) => concatReverse0(Nil(), ys, Cons(y, acc))
      }
      case Cons(x, xs) => concatReverse0(xs, l2, Cons(x, acc))
    }
  //} ensuring(res => listContent(res).size <= listContent(l1).size + listContent(l2).size + listContent(acc).size)
  } ensuring(res => listContent(res) == listContent(l1) ++ listContent(l2) ++ listContent(acc))
}
