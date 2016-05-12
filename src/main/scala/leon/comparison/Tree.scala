package leon.comparison

import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 12.05.16.
  *
  * Basic class just to allow easy store of expressions-tree
  */

case class Tree[T](value: T, children: List[Tree[T]] ) {
  def isLeaf: Boolean = children.isEmpty
  def isNode: Boolean = !isLeaf
  def size: Int = 1 + children.foldLeft(0)( (acc, child) => acc + child.size )

}

/**
  * In fact, having a BadTree and trying to change it for a List[Tree] is just about making all possible
  * combination of children.
  *
  * e.g: BadTree(val, List(List((a,1), (b,2)), List(c,3)))
  *
  * must give List(Tree(val, List((a,1), (c,3))), Tree(val, List((b,2), (c3))))
  *
  * @param value
  * @param listChildren
  * @tparam T
  */
case class BadTree[T](value: T, listChildren: List[List[Tree[T]]]) {
  def toTreeList: List[Tree[T]] = {
    def combine(list: List[List[Tree[T]]]): List[List[Tree[T]]] = list match {
      case Nil => List()
      case x :: xs =>
        for {
          j <- combine(xs)
          i <- x
        } yield i :: j
    }

    combine(listChildren).map(children => Tree(value, children))
  }
}
