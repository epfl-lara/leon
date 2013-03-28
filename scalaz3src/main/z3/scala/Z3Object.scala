package z3.scala

import z3.Z3Wrapper

trait Z3Object {
  val ptr: Long
  val context: Z3Context

  protected[z3] def incRef()
  protected[z3] def decRef()
}

trait Z3ASTLike extends Z3Object {
  final protected[z3] def incRef() {
    Z3Wrapper.incRef(context.ptr, ptr)
  }

  final protected[z3] def decRef() {
    Z3Wrapper.decRef(context.ptr, ptr)
  }
}
