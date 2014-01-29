//package leon
//package smtlib
//
//import purescala._
//import Common._
//import Trees._
//import Extractors._
//import TreeOps._
//import TypeTrees._
//import Definitions._
//
//import _root_.smtlib.sexpr
//import sexpr.SExprs._
//import _root_.smtlib.Commands.{Identifier => SmtLibIdentifier, _}
//
//  // prec: there should be no lets and no pattern-matching in this expression
//  def collectWithPathCondition(matcher: Expr=>Boolean, expression: Expr) : Set[(Seq[Expr],Expr)] = {
//    var collected : Set[(Seq[Expr],Expr)] = Set.empty
//
//      def rec(expr: Expr, path: List[Expr]) : Unit = {
//        if(matcher(expr)) {
//          collected = collected + ((path.reverse, expr))
//        }
//
//        expr match {
//          case Let(i,e,b) => {
//            rec(e, path)
//              rec(b, Equals(Variable(i), e) :: path)
//          }
//          case IfExpr(cond, thn, els) => {
//            rec(cond, path)
//              rec(thn, cond :: path)
//              rec(els, Not(cond) :: path)
//          }
//          case NAryOperator(args, _) => args.foreach(rec(_, path))
//            case BinaryOperator(t1, t2, _) => rec(t1, path); rec(t2, path)
//            case UnaryOperator(t, _) => rec(t, path)
//          case t : Terminal => ;
//          case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
//        }
//      }
//
//    rec(expression, Nil)
//      collected
//  }
//}
