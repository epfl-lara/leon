package leon
package purescala


import Expressions._
import Types._
import Common._

trait ExpressionsBuilder {

  protected def i(i: Int) = InfiniteIntegerLiteral(i)
  protected def r(x: Double) = RealLiteral(BigDecimal(x))
  protected def v(name: String, tpe: TypeTree = IntegerType) = Variable(FreshIdentifier(name, tpe))

  protected val xId = FreshIdentifier("x", RealType)
  protected val x = Variable(xId)
  protected val yId = FreshIdentifier("y", RealType)
  protected val y = Variable(yId)
  protected val zId = FreshIdentifier("z", RealType)
  protected val z = Variable(zId)


  protected val aId = FreshIdentifier("a", IntegerType)
  protected val a = Variable(aId)
  protected val bId = FreshIdentifier("b", IntegerType)
  protected val b = Variable(bId)
  protected val cId = FreshIdentifier("c", IntegerType)
  protected val c = Variable(cId)

  protected val mId = FreshIdentifier("m", IntegerType)
  protected val m = Variable(mId)
  protected val nId = FreshIdentifier("n", IntegerType)
  protected val n = Variable(nId)
  protected val kId = FreshIdentifier("k", IntegerType)
  protected val k = Variable(kId)


  protected val pId = FreshIdentifier("p", BooleanType)
  protected val p = Variable(pId)
  protected val qId = FreshIdentifier("q", BooleanType)
  protected val q = Variable(qId)
  protected val rId = FreshIdentifier("r", BooleanType)
  protected val r = Variable(rId)

}
