package z3.scala

import z3.Z3Wrapper

class Z3Tactic private[z3](val ptr : Long, val context : Z3Context) extends Z3Object {
  override def equals(that : Any) : Boolean = {
    that != null &&
      that.isInstanceOf[Z3Tactic] && {
      val that2 = that.asInstanceOf[Z3Tactic]
      that2.ptr == this.ptr // && context.isEqAST(this, that2)
    }
  }

  def incRef() {
    Z3Wrapper.tacticIncRef(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.tacticDecRef(context.ptr, this.ptr)
  }

  locally {
    context.tacticQueue.incRef(this)
  }

  override def finalize() {
    context.tacticQueue.decRef(this)
  }
}
