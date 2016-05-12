package leon.comparison

import leon.purescala.Expressions._

/**
  * Created by joachimmuth on 12.05.16.
  *
  * Basic class just to allow easy store of expressions-tree
  */

case class Tree(value: Expr, children: List[Tree] ) {
  def isLeaf: Boolean = children.isEmpty
  def isNode: Boolean = !isLeaf
  def size: Int = 1 + children.foldLeft(0)( (acc, child) => acc + child.size )

}