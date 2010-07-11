package orderedsets

object DNF {
  import purescala.Trees._
  import TreeOperations.dnf


  // Printer (both && and || are printed as ? on windows..)
  def pp(expr: Expr): String = expr match {
    case And(es) => (es map pp).mkString("( ", " & ", " )")
    case Or(es) => (es map pp).mkString("( ", " | ", " )")
    case Not(e) => "!(" + pp(e) + ")"
    case _ => expr.toString
  }

  // Tests
  import purescala.Common._
  implicit def str2id(str: String): Identifier = FreshIdentifier(str)

  val a = Variable("a")
  val b = Variable("b")
  val c = Variable("c")
  val x = Variable("x")
  val y = Variable("y")
  val z = Variable("z")

  val t1 = And(Or(a, b), Or(x, y))
  val t2 = Implies(x, Iff(y, z))

  def main(args: Array[String]) {

    test(t1)
    test(t2)
    test(Not(t1))
    test(Not(t2))
  }

  def test(before: Expr) {
    val after = Or((dnf(before) map And.apply).toSeq)
    println
    println("Before dnf : " + pp(before))
    //println("After dnf  : " + pp(after))
    println("After dnf  : ")
    for (and <- dnf(before)) println("  " + pp(And(and)))
  }


}