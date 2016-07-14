/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package unrolling

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Constructors._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._
import purescala.TypeOps.bestRealType

import utils._
import utils.SeqUtils._
import Instantiation._
import Template._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

case class FreshFunction(expr: Expr) extends Expr with Extractable {
  val getType = BooleanType
  val extract = Some(Seq(expr), (exprs: Seq[Expr]) => FreshFunction(exprs.head))
}

object DatatypeTemplate {

  def apply[T](
    encoder: TemplateEncoder[T],
    manager: DatatypeManager[T],
    tpe: TypeTree
  ) : DatatypeTemplate[T] = {
    val id = FreshIdentifier("x", tpe, true)
    val expr = matchToIfThenElse(manager.typeUnroller(Variable(id)))

    val pathVar = FreshIdentifier("b", BooleanType, true)

    var condVars = Map[Identifier, T]()
    var condTree = Map[Identifier, Set[Identifier]](pathVar -> Set.empty).withDefaultValue(Set.empty)
    def storeCond(pathVar: Identifier, id: Identifier): Unit = {
      condVars += id -> encoder.encodeId(id)
      condTree += pathVar -> (condTree(pathVar) + id)
    }

    var guardedExprs = Map[Identifier, Seq[Expr]]()
    def storeGuarded(pathVar: Identifier, expr: Expr): Unit = {
      val prev = guardedExprs.getOrElse(pathVar, Nil)
      guardedExprs += pathVar -> (expr +: prev)
    }

    def requireDecomposition(e: Expr): Boolean = exists {
      case _: FunctionInvocation => true
      case _ => false
    } (e)

    def rec(pathVar: Identifier, expr: Expr): Unit = expr match {
      case i @ IfExpr(cond, thenn, elze) if requireDecomposition(i) =>
        val newBool1: Identifier = FreshIdentifier("b", BooleanType, true)
        val newBool2: Identifier = FreshIdentifier("b", BooleanType, true)

        storeCond(pathVar, newBool1)
        storeCond(pathVar, newBool2)

        storeGuarded(pathVar, or(Variable(newBool1), Variable(newBool2)))
        storeGuarded(pathVar, or(not(Variable(newBool1)), not(Variable(newBool2))))
        storeGuarded(pathVar, Equals(Variable(newBool1), cond))

        rec(newBool1, thenn)
        rec(newBool2, elze)

      case a @ And(es) if requireDecomposition(a) =>
        val partitions = groupWhile(es)(!requireDecomposition(_))
        for (e <- partitions.map(andJoin)) rec(pathVar, e)

      case _ =>
        storeGuarded(pathVar, expr)
    }

    rec(pathVar, expr)

    val (idT, pathVarT) = (encoder.encodeId(id), encoder.encodeId(pathVar))
    val (clauses, blockers, _, functions, _, _) = Template.encode(encoder,
      pathVar -> pathVarT, Seq(id -> idT), condVars, Map.empty, guardedExprs, Seq.empty, Seq.empty)

    new DatatypeTemplate[T](encoder, manager,
      pathVar -> pathVarT, idT, condVars, condTree, clauses, blockers, functions)
  }
}

class DatatypeTemplate[T] private (
  val encoder: TemplateEncoder[T],
  val manager: DatatypeManager[T],
  val pathVar: (Identifier, T),
  val argument: T,
  val condVars: Map[Identifier, T],
  val condTree: Map[Identifier, Set[Identifier]],
  val clauses: Seq[T],
  val blockers: Map[T, Set[TemplateCallInfo[T]]],
  val functions: Set[(T, FunctionType, T)]) extends Template[T] {

  val args = Seq(argument)
  val exprVars = Map.empty[Identifier, T]
  val applications = Map.empty[T, Set[App[T]]]
  val lambdas = Seq.empty[LambdaTemplate[T]]
  val matchers = Map.empty[T, Set[Matcher[T]]]
  val quantifications = Seq.empty[QuantificationTemplate[T]]

  def instantiate(blocker: T, arg: T): Instantiation[T] = instantiate(blocker, Seq(Left(arg)))
}

class DatatypeManager[T](encoder: TemplateEncoder[T]) extends TemplateManager(encoder) {

  private val classCache: MutableMap[ClassType, FunDef] = MutableMap.empty

  private def classTypeUnroller(ct: ClassType): FunDef = classCache.get(ct) match {
    case Some(fd) => fd
    case None =>
      val param = ValDef(FreshIdentifier("x", ct))
      val fd = new FunDef(FreshIdentifier("unroll"+ct.classDef.id), Seq.empty, Seq(param), BooleanType)
      classCache += ct -> fd

      val matchers = ct match {
        case (act: AbstractClassType) => act.knownCCDescendants
        case (cct: CaseClassType) => Seq(cct)
      }

      fd.body = Some(MatchExpr(param.toVariable, matchers.map { cct =>
        val pattern = CaseClassPattern(None, cct, cct.fields.map(vd => WildcardPattern(Some(vd.id))))
        val expr = andJoin(cct.fields.map(vd => typeUnroller(Variable(vd.id))))
        MatchCase(pattern, None, expr)
      }))

      fd
  }

  private val requireChecking: MutableSet[ClassType] = MutableSet.empty
  private val requireCache: MutableMap[TypeTree, Boolean] = MutableMap.empty

  private def requireTypeUnrolling(tpe: TypeTree): Boolean = requireCache.get(tpe) match {
    case Some(res) => res
    case None =>
      val res = tpe match {
        case ft: FunctionType => true
        case ct: CaseClassType if ct.classDef.hasParent => true
        case ct: ClassType if requireChecking(ct.root) => false
        case ct: ClassType =>
          requireChecking += ct.root
          val classTypes = ct.root +: (ct.root match {
            case (act: AbstractClassType) => act.knownDescendants
            case (cct: CaseClassType) => Seq.empty
          })

          classTypes.exists(ct => ct.classDef.hasInvariant || ct.fieldsTypes.exists(requireTypeUnrolling))

        case BooleanType | UnitType | CharType | IntegerType |
             RealType | Int32Type | StringType | (_: TypeParameter) => false

        case at: ArrayType => true

        case NAryType(tpes, _) => tpes.exists(requireTypeUnrolling)
      }

      requireCache += tpe -> res
      res
  }

  def typeUnroller(expr: Expr): Expr = expr.getType match {
    case tpe if !requireTypeUnrolling(tpe) =>
      BooleanLiteral(true)

    case ct: ClassType =>
      val inv = if (ct.classDef.root.hasInvariant) {
        Seq(FunctionInvocation(ct.root.invariant.get, Seq(expr)))
      } else {
        Seq.empty
      }

      val subtype = if (ct != ct.root) {
        Seq(IsInstanceOf(expr, ct))
      } else {
        Seq.empty
      }

      val induct = if (!ct.classDef.isInductive) {
        val matchers = ct.root match {
          case (act: AbstractClassType) => act.knownCCDescendants
          case (cct: CaseClassType) => Seq(cct)
        }

        val cases = matchers.map { cct =>
          val pattern = CaseClassPattern(None, cct, cct.fields.map(vd => WildcardPattern(Some(vd.id))))
          val expr = andJoin(cct.fields.map(vd => typeUnroller(Variable(vd.id))))
          MatchCase(pattern, None, expr)
        }

        if (cases.forall(_.rhs == BooleanLiteral(true))) None else Some(MatchExpr(expr, cases))
      } else {
        val fd = classTypeUnroller(ct.root)
        Some(FunctionInvocation(fd.typed, Seq(expr)))
      }

      andJoin(inv ++ subtype ++ induct)

    case TupleType(tpes) =>
      andJoin(tpes.zipWithIndex.map(p => typeUnroller(TupleSelect(expr, p._2 + 1))))

    case FunctionType(_, _) =>
      FreshFunction(expr)

    case at: ArrayType =>
      GreaterEquals(ArrayLength(expr), IntLiteral(0))

    case _ => scala.sys.error("TODO")
  }

  private val typeCache: MutableMap[TypeTree, DatatypeTemplate[T]] = MutableMap.empty

  protected def typeTemplate(tpe: TypeTree): DatatypeTemplate[T] = typeCache.getOrElse(tpe, {
    val template = DatatypeTemplate(encoder, this, tpe)
    typeCache += tpe -> template
    template
  })
}

