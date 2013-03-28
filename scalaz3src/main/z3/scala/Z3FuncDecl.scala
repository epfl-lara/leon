package z3.scala

import z3.Pointer

// We store the arity when it's known to help preventing segfaults...
sealed class Z3FuncDecl private[z3](val ptr: Long, val arity: Int, val context: Z3Context) extends Z3ASTLike {
  def apply(args: Z3AST*) : Z3AST = context.mkApp(this, args:_*)

  lazy val getName: Z3Symbol = context.getDeclName(this)

  def getDomainSize : Int = arity

  def getDomain(i: Int) : Z3Sort = context.getDomain(this, i)

  lazy val getRange : Z3Sort = context.getRange(this)

//  override def equals(that: Any) : Boolean = {
//    if(that == null) false else (that.isInstanceOf[Z3FuncDecl] && this.ptr == that.asInstanceOf[Z3FuncDecl].ptr)
//  }

  override def equals(that: Any) : Boolean = {
    that != null && that.isInstanceOf[Z3FuncDecl] && context.isEqFuncDecl(this, that.asInstanceOf[Z3FuncDecl])
  }

  private lazy val hc : Int = 0
  override def hashCode : Int = hc

  override def toString : String = context.funcDeclToString(this)

  locally {
    context.astQueue.incRef(this)
  }

  override def finalize() {
    context.astQueue.decRef(this)
  }
}
