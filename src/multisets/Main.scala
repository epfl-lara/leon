package multisets

import purescala.Extensions.Solver
import purescala.Reporter
import purescala.Trees._

import scala.collection.mutable.Set



class Main(reporter: Reporter) extends Solver(reporter) {
  val description = "Multiset Solver"
  Global.reporter = reporter



  def createFormulaThatSomethingsIsSet(s:String):FormulaIn = {
    val a1 = FIAtom(AIEq(TIMultiplicity(s), TIConstant(1)))
    val a0 = FIAtom(AIEq(TIMultiplicity(s), TIConstant(0)))
    FIOr(a1, a0)
  }


  def constructFormulaInAboutSets(s:Set[String]):FormulaIn = {
    val sl = s.toList
    val h = sl.head
    val t = sl.tail
    var f = createFormulaThatSomethingsIsSet(h)
    t.foreach(e => {
      val ft = createFormulaThatSomethingsIsSet(e)
      f = FIAnd(f, ft)
    })
    f
  }

  def constructFormulaAboutSets(s:Set[String]):Formula = {
    val f1 = constructFormulaInAboutSets(s)
    FAtom(AForAllElem(f1))
  }

  def createFormula(p:(Formula,Set[String])):Formula = {
    val f1 = p._1
    val s = p._2
    val f = if (s.isEmpty) f1 else {
      val f2 = constructFormulaAboutSets(s)
      FAnd(f1, f2) 
    }
    f
  }


  def solve(expr: Expr) : Option[Boolean] = {
    val mt = multisets.MainAST2MultisetsTranslator.translate(negate(expr))
    val mf = mt.map(p => createFormula(p))
    val res = mf.map(f => !MAPARun.executeOneFormula("f", f))
    res
    }
}

object Global {
  var reporter: Reporter = null
}
