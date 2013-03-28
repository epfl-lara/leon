package z3.scala

import z3.{Z3Wrapper,Pointer}

sealed class Z3Literals private[z3](val ptr: Long, context: Z3Context) {
  def delete : Unit = {
    Z3Wrapper.delLiterals(context.ptr, this.ptr)
  }

  def getNumLiterals : Int = context.getNumLiterals(this) 

//  def getLabelSymbol(idx : Int) : Z3Symbol = context.getLabelSymbol(this, idx)

  def getLiterals : Iterator[Z3AST] = new Iterator[Z3AST] {
    val total : Int = getNumLiterals
    var returned : Int = 0

    override def hasNext : Boolean = (returned < total)
    override def next() : Z3AST = {
      val toReturn = getLiteral(returned)
      returned += 1
      toReturn
    }
  }

  def getLiteral(idx : Int) : Z3AST = context.getLiteral(this, idx)

  def disableLiteral(idx : Int) : Unit = context.disableLiteral(this, idx)

  def block : Unit = context.blockLiterals(this)

}
