package leon.comparison

/**
  * Created by joachimmuth on 12.05.16.
  *
  * Basic class just to allow easy store of expressions-tree
  */

case class myTree[T](value: T, children: List[myTree[T]]) {
  def isLeaf: Boolean = children.isEmpty

  def isNode: Boolean = !isLeaf

  def size: Int = 1 + children.foldLeft(0)((acc, child) => acc + child.size)

  def toList: List[T] = value +: children.flatMap(child => child.toList)
}
