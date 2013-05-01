package z3.scala

import z3.Pointer

sealed class Z3Sort private[z3](val ptr: Long, val context: Z3Context) extends Z3ASTLike {
  override def equals(that: Any) : Boolean = {
    that != null && that.isInstanceOf[Z3Sort] && context.isEqSort(this, that.asInstanceOf[Z3Sort])
  }

  override def toString : String = context.sortToString(this)

  lazy val isBoolSort : Boolean = context.isEqSort(this, context.mkBoolSort)
  lazy val isIntSort : Boolean = context.isEqSort(this, context.mkIntSort)
  lazy val isIntSetSort : Boolean = context.isEqSort(this, context.mkSetSort(context.mkIntSort))
  lazy val isRealSort : Boolean = context.isEqSort(this, context.mkRealSort)

  locally {
    context.astQueue.incRef(this)
  }

  override def finalize() {
    context.astQueue.decRef(this)
  }
}
