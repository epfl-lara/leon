package leon
package purescala


import Expressions._
import Types._
import Common._

trait ExpressionsBuilder {

  protected def i(x: Int) = InfiniteIntegerLiteral(x)
  protected def v(name: String, tpe: TypeTree = IntegerType) = Variable(FreshIdentifier(name, tpe))

  protected val xId = FreshIdentifier("x", IntegerType)
  protected val x = Variable(xId)
  protected val yId = FreshIdentifier("y", IntegerType)
  protected val y = Variable(yId)
  protected val zId = FreshIdentifier("z", IntegerType)
  protected val z = Variable(zId)

  protected val aId = FreshIdentifier("a", IntegerType)
  protected val a = Variable(aId)
  protected val bId = FreshIdentifier("b", IntegerType)
  protected val b = Variable(bId)
  protected val cId = FreshIdentifier("c", IntegerType)
  protected val c = Variable(cId)

  protected val pId = FreshIdentifier("p", BooleanType)
  protected val p = Variable(pId)
  protected val qId = FreshIdentifier("q", BooleanType)
  protected val q = Variable(qId)
  protected val rId = FreshIdentifier("r", BooleanType)
  protected val r = Variable(rId)
}
