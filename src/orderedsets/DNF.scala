package orderedsets

object DNF {

  import purescala.Trees._

  def dnf(expr: Expr): Stream[And] = _dnf(expr) map And.apply
     
  private def _dnf(expr: Expr): Stream[Seq[Expr]] = expr match {
    case And(Nil) => Stream(Nil)
    case And(c :: Nil) => _dnf(c)
    case And(c :: cs) =>
      for (conj1 <- _dnf(c); conj2 <- _dnf(And(cs)))
        yield conj1 ++ conj2
    case Or(Nil) => Stream(Seq(BooleanLiteral(false)))
    case Or(d :: Nil) => _dnf(d)
    case Or(d :: ds) => _dnf(d) append _dnf(Or(ds))
    // Rewrite Iff and Implies
    case Iff(p, q) =>
      _dnf(Or(And(p, q), And(negate(p), negate(q))))
    case Implies(p, q) =>
      _dnf(Or(negate(p), q))
    // Convert to nnf
    case Not(e@(And(_) | Or(_) | Iff(_, _) | Implies(_, _))) =>
      _dnf(negate(e))
    case _ => Stream(expr :: Nil)
  }
  
  // Printer (both && and || are printed as ? on windows..)
  def pp(expr: Expr): String = expr match {
  	case And(es) => (es map pp).mkString("( "," & "," )")
  	case Or(es) => (es map pp).mkString("( "," | "," )")
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
  
  val t1 = And(Or(a, b),Or(x,y))
  val t2 = Implies(x,Iff(y,z))
  
  def main(args: Array[String]) {
  	
  	test(t1)
  	test(t2)
  	test(Not(t1))
  	test(Not(t2))
  }
  
  def test(before: Expr) {
  	val after = Or(dnf(before).toSeq)
  	println
  	println("Before dnf : " + pp(before))
  	//println("After dnf  : " + pp(after))
  	println("After dnf  : ")
  	for (and <- dnf(before)) println("  " + pp(and))
  }
}