package z3.scala

import z3.Pointer

sealed class Z3AST private[z3](val ptr : Long, val context : Z3Context) extends Z3ASTLike {
  override def equals(that : Any) : Boolean = {
    that != null &&
    that.isInstanceOf[Z3AST] && {
      val that2 = that.asInstanceOf[Z3AST]
      that2.ptr == this.ptr // && context.isEqAST(this, that2)
    }
  }

  private lazy val hc : Int = (ptr >> 4).toInt
  override def hashCode : Int = hc
  override def toString : String = context.astToString(this)

  lazy val getSort : Z3Sort = context.getSort(this)

  def ===(that: Z3AST): Z3AST = context.mkEq(this, that)
  def !==(that: Z3AST): Z3AST = context.mkDistinct(this, that)

  import dsl.{Tree,TopSort,BoolSort,BottomSort,Z3ASTWrapper,Eq,Distinct}
  def ===(that: Tree[_ >: BottomSort <: TopSort]): Tree[BoolSort] = Eq(Z3ASTWrapper[BottomSort](this), that)
  def !==(that: Tree[_ >: BottomSort <: TopSort]): Tree[BoolSort] = Distinct(Z3ASTWrapper[BottomSort](this), that)


  locally {
    context.astQueue.incRef(this)
  }

  override def finalize() {
    context.astQueue.decRef(this)
  }
}
