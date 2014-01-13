package leon
package purescala

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.Common._
import purescala.Definitions._

object HOTreeOps {
  import scala.collection.mutable.{Map => MutableMap}

  sealed abstract class Caller
  case class VariableCaller(id: Identifier) extends Caller
  case class InvocationCaller(funDef: FunDef) extends Caller
  case class AnonymousCaller(anon: AnonymousFunction) extends Caller

  def app2CallerWithLevel(app: FunctionApplication): (Caller,Int) = app.function match {
    case f @ FunctionApplication(_, _) =>
      val (caller, lvl) = app2CallerWithLevel(f)
      caller -> (lvl + 1)
    case a @ AnonymousFunction(_, _) => AnonymousCaller(a) -> 1
    case FunctionInvocation(fd, _) => InvocationCaller(fd) -> 1
    case Variable(id) => VariableCaller(id) -> 1
  }

  def app2Caller(app: FunctionApplication) = app2CallerWithLevel(app)._1

  def app2ID(app: FunctionApplication) = app2Caller(app) match {
    case VariableCaller(id) => id
    case InvocationCaller(fd) => fd.id
    case c => scala.sys.error("Unexpected caller : " + c)
  }

  /*
  def killFunctionsInCondition(expr: Expr) = expr match {
    case And(es) => And(es collect { case e if !contains(e, _.isInstanceOf[FunctionApplication]) => e})
    case e if !contains(e, _.isInstanceOf[FunctionApplication]) => e
    case _ => BooleanLiteral(true)
  }
  */

  def hoistHOIte(expr: Expr) = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(ife @ IfExpr(c, t, e), op) if ife.getType.isInstanceOf[FunctionType] =>
        Some(IfExpr(c, op(t).setType(uop.getType), op(e).setType(uop.getType)).setType(uop.getType))
      case bop@BinaryOperator(ife @ IfExpr(c, t, e), t2, op) if ife.getType.isInstanceOf[FunctionType] =>
        Some(IfExpr(c, op(t, t2).setType(bop.getType), op(e, t2).setType(bop.getType)).setType(bop.getType))
      case bop@BinaryOperator(t1, ife @ IfExpr(c, t, e), op) if ife.getType.isInstanceOf[FunctionType] =>
        Some(IfExpr(c, op(t1, t).setType(bop.getType), op(t1, e).setType(bop.getType)).setType(bop.getType))
      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere {
          case ife @ IfExpr(_, _, _) if ife.getType.isInstanceOf[FunctionType] => true
          case _ => false
        }
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

    fixpoint(postMap(transform))(expr)
  }

  def expandHOLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) =>
        if (i.getType.isInstanceOf[FunctionType]) rec(b, s + (i -> rec(e, s)))
        else Let(i, rec(e,s), rec(b,s))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1,s), rec(t2,s), rec(t3,s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut,s), cses.map(inCase(_, s))).setType(m.getType).setPos(m)
      case n @ NAryOperator(args, recons) => {
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a, s)
          if (ra != a) {
            change = true
            ra
          } else {
            a
          }
        })
        if (change) recons(rargs).setType(n.getType)
        else n
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1, s)
        val r2 = rec(t2, s)
        if (r1 != t1 || r2 != t2) recons(r1, r2).setType(b.getType)
        else b
      }
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t, s)
        if (r != t) recons(r).setType(u.getType)
        else u
      }
      case t: Terminal => t
      case unhandled => scala.sys.error("Unhandled case in expandHOLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs, s))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard, s), rec(rhs, s))
    }

    rec(expr, Map.empty)
  }

  private val applicationArgsCache : MutableMap[TypeTree,Seq[Identifier]] = MutableMap()
  def buildApplicationArgs(tpe: TypeTree): Seq[Identifier] = applicationArgsCache.get(tpe) match {
    case Some(ids) => ids
    case None =>
      val seq = tpe match {
        case FunctionType(argTypes, returnType) =>
          argTypes.map(FreshIdentifier("x", true).setType(_)) ++ buildApplicationArgs(returnType)
        case _ => Seq()
      }
      applicationArgsCache(tpe) = seq
      seq
  }

  def buildApplication(expr: Expr, args: Seq[Expr]): Expr = expr.getType match {
    case FunctionType(argTypes, returnType) =>
      val (currentArgs, nextArgs) = args.splitAt(argTypes.size)
      val application = FunctionApplication(expr, currentArgs)
      buildApplication(application, nextArgs)
    case tpe =>
      assert(args.isEmpty && !tpe.isInstanceOf[FunctionType])
      expr
  }

  def buildAnonymous(expr: Expr, args: Seq[Identifier]): Expr = expr.getType match {
    case FunctionType(argTypes, returnType) =>
      val (currentArgs, nextArgs) = args.splitAt(argTypes.size)
      val application = FunctionApplication(expr, currentArgs.map(_.toVariable))
      AnonymousFunction(currentArgs.map(id => VarDecl(id, id.getType)), buildAnonymous(application, nextArgs))
    case tpe =>
      assert(args.isEmpty && !tpe.isInstanceOf[FunctionType])
      expr
  }

  def extractToAnonymous(expr: Expr) = {
    def extract(expr: Expr, build: Boolean) =
      if (build) buildAnonymous(expr, buildApplicationArgs(expr.getType)) else expr

    def rec(expr: Expr, build: Boolean): Expr = expr match {
      case FunctionApplication(caller, args) =>
        val newArgs = args.map(rec(_, true))
        val newCaller = rec(caller, false)
        extract(FunctionApplication(newCaller, newArgs), build)
      case FunctionInvocation(fd, args) =>
        val newArgs = args.map(rec(_, true))
        extract(FunctionInvocation(fd, newArgs), build)
      case af @ AnonymousFunction(args, body) => af
      case NAryOperator(es, recons) => recons(es.map(rec(_, build)))
      case BinaryOperator(e1, e2, recons) => recons(rec(e1, build), rec(e2, build))
      case UnaryOperator(e, recons) => recons(rec(e, build))
      case t: Terminal => t
    }

    rec(expr, true)
  }

  def applyAnonymous(expr: Expr) = postMap({
    case FunctionApplication(AnonymousFunction(fargs, body), args) =>
      Some(replaceFromIDs(Map(fargs.map(_.id) zip args : _*), body))
    case _ => None
  })(expr)

  def preProcess(expr: Expr) = {
    extractToAnonymous(
      applyAnonymous(
        hoistHOIte(
          expandHOLets(
            simplifyLets(
              matchToIfThenElse(
                expr
              )
            )
          )
        )
      )
    )
  }
}
