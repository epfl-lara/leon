package z3.scala

import z3.Z3Wrapper
import scala.collection.SeqLike

final class Z3ASTVector private[z3](val ptr : Long, val context : Z3Context) extends Z3Object {

  def incRef() {
    Z3Wrapper.astvectorIncRef(context.ptr, this.ptr)
  }

  def decRef() {
    Z3Wrapper.astvectorDecRef(context.ptr, this.ptr)
  }

  def get(i: Int): Z3AST = {
    new Z3AST(Z3Wrapper.astvectorGet(context.ptr, this.ptr, i), context)
  }

  def set(i: Int, v: Z3AST) {
    Z3Wrapper.astvectorSet(context.ptr, this.ptr, i, v.ptr)
  }

  def size: Int = {
    Z3Wrapper.astvectorSize(context.ptr, this.ptr)
  }

  // Utility functions
  def apply(i: Int): Z3AST = {
    get(i)
  }

  def update(i: Int, v: Z3AST) = {
    set(i, v)
  }

  def toSeq: Seq[Z3AST] = {
    for (i <- 0 until size) yield {
      get(i)
    }
  }

  locally {
    context.astvectorQueue.incRef(this)
  }

  override def finalize() {
    context.astvectorQueue.decRef(this)
  }
}
