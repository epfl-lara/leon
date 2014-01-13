package leon
package termination

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import purescala.Common._

import scala.collection.mutable.{Map => MutableMap}

trait StructuralSize {

  private val sizeCache : MutableMap[TypeTree, FunDef] = MutableMap.empty

  def size(expr: Expr) : Expr = {
    def funDef(ct: ClassType, cases: ClassType => Seq[MatchCase]): FunDef = {
      // we want to reuse generic size functions for sub-types
      val argumentType = ct match {
        case (cct : CaseClassType) if cct.parent.isDefined =>
          val classDef = cct.parent.get.classDef
          classDefToClassType(classDef, classDef.tparams.map(_.toType))
        case (ct : ClassType) =>
          classDefToClassType(ct.classDef, ct.classDef.tparams.map(_.toType))
      }

      sizeCache.get(argumentType) match {
        case Some(fd) => fd
        case None =>
          val argument = VarDecl(FreshIdentifier("x").setType(argumentType), argumentType)
          val fd = new FunDef(FreshIdentifier("size", true), Int32Type, Seq(argument))
          sizeCache(argumentType) = fd

          val body = simplifyLets(matchToIfThenElse(MatchExpr(argument.toVariable, cases(argumentType))))
          val postId = FreshIdentifier("res", false).setType(Int32Type)
          val postSubcalls = functionCallsOf(body).map(GreaterThan(_, IntLiteral(0))).toSeq
          val postRecursive = GreaterThan(Variable(postId), IntLiteral(0))
          val postcondition = And(postSubcalls :+ postRecursive)

          fd.body = Some(body)
          fd.postcondition = Some(postId, postcondition)
          fd
      }
    }

    def caseClassType2MatchCase(_c: ClassType): MatchCase = {
      val c = _c.asInstanceOf[CaseClassType] // required by leon framework
      val arguments = c.fields.map(f => f -> f.id.freshen)
      val argumentPatterns = arguments.map(p => WildcardPattern(Some(p._2)))
      val sizes = arguments.map(p => size(Variable(p._2)))
      val result = sizes.foldLeft[Expr](IntLiteral(1))(Plus(_,_))
      SimpleCase(CaseClassPattern(None, c, argumentPatterns), result)
    }

    expr.getType match {
      case (ct: ClassType) => FunctionInvocation(funDef(ct, _ match {
        case (act: AbstractClassType) => act.knownChildren map caseClassType2MatchCase
        case (cct: CaseClassType) => Seq(caseClassType2MatchCase(cct))
      }), Seq(expr))
      case TupleType(argTypes) => argTypes.zipWithIndex.map({
        case (_, index) => size(TupleSelect(expr, index + 1))
      }).foldLeft[Expr](IntLiteral(0))(Plus(_,_))
      case _ => IntLiteral(0)
    }
  }

  def defs : Set[FunDef] = Set(sizeCache.values.toSeq : _*)
}

// vim: set ts=4 sw=4 et:
