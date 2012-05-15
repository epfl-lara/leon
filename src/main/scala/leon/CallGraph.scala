package leon

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Common._

class CallGraph(val program: Program) {

  sealed abstract class ProgramPoint
  case class FunctionStart(fd: FunDef) extends ProgramPoint
  case class ExpressionPoint(wp: Expr) extends ProgramPoint

  //sealed abstract class EdgeLabel
  //case class ConditionLabel(expr: Expr) extends EdgeLabel {
  //  require(expr.getType == BooleanType)
  //}
  //case class FunctionInvocLabel(fd: FunDef, args: List[Expr]) extends EdgeLabel {
  //  require(args.zip(fd.args).forall(p => p._1.getType == p._2.getType))
  //}
  case class TransitionLabel(cond: Expr, assignment: Map[Variable, Expr])

  private lazy val graph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = buildGraph


  private def buildGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    //var fd2point: Map[FunDef, ProgramPoint] = Map()

    program.definedFunctions.foreach(fd => {
      val body = fd.body.get 
      //val cleanBody = hoistIte(expandLets(matchToIfThenElse(body)))
      val cleanBody = expandLets(matchToIfThenElse(body))
    //  collectWithPathCondition(cleanBody).foreach{
    //    case (path, WayPoint) =>

    })

    null
  }

  private def collectWithPathCondition(expression: Expr, startingPoint: ProgramPoint): Map[ProgramPoint, (ProgramPoint, Set[TransitionLabel])] = {
    var callGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = Map()

    def rec(expr: Expr, path: List[Expr], startingPoint: ProgramPoint): Unit = expr match {
      case FunctionInvocation(fd, args) => {
        val transitions: Set[(ProgramPoint, TransitionLabel)] = callGraph.get(startingPoint) match {
          case None => Set()
          case Some(s) => s
        }
        val newPoint = FunctionStart(fd)
        val newTransition = TransitionLabel(And(path.toSeq), fd.args.zip(args).map{ case (VarDecl(id, _), arg) => (id.toVariable, arg) }.toMap)
        callGraph += (startingPoint -> (transitions + (newPoint, newTransition)))
        args.foreach(arg => rec(arg, startingPoint, startingPoint))
      }
      case WayPoint(e) => {
        val transitions: Set[(ProgramPoint, TransitionLabel)] = callGraph.get(startingPoint) match {
          case None => Set()
          case Some(s) => s
        }
        val newPoint = ExpressionPoint(expr)
        val newTransition = TransitionLabel(And(path.toSeq), fd.args.zip(args).map{ case (VarDecl(id, _), arg) => (id.toVariable, arg) }.toMap)
        callGraph += (startingPoint -> (transitions + (newPoint, newTransition)))
        rec(e, List(), newPoint)
      }
      case IfExpr(cond, then, elze) => {
        rec(cond, path, startingPoint)
        rec(then, cond :: path, startingPoint) 
        rec(elze, Not(cond) :: path, startingPoint)
      }
      case NAryOperator(args, _) => args.foreach(rec(_, path, startingPoint))
      case BinaryOperator(t1, t2, _) => rec(t1, path, startingPoint); rec(t2, path, startingPoint)
      case UnaryOperator(t, _) => rec(t, path, startingPoint)
      case t : Terminal => ;
      case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
    }

    rec(expression, List(), startingPoint)
    callGraph
  }


  //guarentee that all IfExpr will be at the top level and as soon as you encounter a non-IfExpr, then no more IfExpr can be find in the sub-expressions
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(IfExpr(c, t, e), op) => Some(IfExpr(c, op(t).setType(uop.getType), op(e).setType(uop.getType)).setType(uop.getType))
      case bop@BinaryOperator(IfExpr(c, t, e), t2, op) => Some(IfExpr(c, op(t, t2).setType(bop.getType), op(e, t2).setType(bop.getType)).setType(bop.getType))
      case bop@BinaryOperator(t1, IfExpr(c, t, e), op) => Some(IfExpr(c, op(t1, t).setType(bop.getType), op(t1, e).setType(bop.getType)).setType(bop.getType))
      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).setType(nop.getType),
            op(beforeIte ++ Seq(e) ++ afterIte).setType(nop.getType)
          ).setType(nop.getType))
        }
      }
      case _ => None
    }

    def fix[A](f: (A) => A, a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f, na)
    }
    fix(searchAndReplaceDFS(transform), expr)
  }

  //def analyse(program: Program) {
  //  z3Solver.setProgram(program)
  //  reporter.info("Running test generation")
  //  val allFuns = program.definedFunctions
  //  allFuns.foreach(fd => {
  //    val testcases = generateTestCases(fd)
  //    reporter.info("Running " + fd.id + " with the following testcases:\n")
  //    reporter.info(testcases.mkString("\n"))
  //  })
  //}

  //private def generatePathConditions(funDef: FunDef): Seq[Expr] = if(!funDef.hasImplementation) Seq() else {
  //  val body = funDef.body.get
  //  val cleanBody = expandLets(matchToIfThenElse(body))
  //  collectWithPathCondition(cleanBody)
  //}

}

  //def hoistIte(expr: Expr): (Seq[Expr] => Expr, Seq[Expr]) = expr match { 
  //  case ite@IfExpr(c, t, e) => {
  //    val (iteThen, valsThen) = hoistIte(t)
  //    val nbValsThen = valsThen.size
  //    val (iteElse, valsElse) = hoistIte(e)
  //    val nbValsElse = valsElse.size
  //    def ite(es: Seq[Expr]): Expr = {
  //      val argsThen = es.take(nbValsThen)
  //      val argsElse = es.drop(nbValsThen)
  //      IfExpr(c, iteThen(argsThen), iteElse(argsElse), e2)
  //    }
  //    (ite, valsThen ++ valsElse)
  //  }
  //  case BinaryOperator(t1, t2, op) => {
  //    val (iteLeft, valsLeft) = hoistIte(t1)
  //    val (iteRight, valsRight) = hoistIte(t2)
  //    def ite(e1: Expr, e2: Expr): Expr = {

  //    }
  //    iteLeft(
  //      iteRight(
  //        op(thenValRight, thenValLeft),
  //        op(thenValRight, elseValLeft)
  //      ), iteRight(
  //        op(elseValRight, thenValLeft),
  //        op(elseValRight, elseValLeft)
  //      )
  //    )
  //  }
  //  case NAryOperator(args, op) => {

  //  }
  //  case (t: Terminal) => {
  //    def ite(es: Seq[Expr]): Expr = {
  //      require(es.size == 1)
  //      es.head
  //    }
  //    (ite, Seq(t))
  //  }
  //  case _ => scala.sys.error("Unhandled tree in hoistIte : " + expr)
  //}

