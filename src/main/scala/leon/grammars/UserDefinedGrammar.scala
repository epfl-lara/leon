/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import aspects._

import purescala.Expressions._
import purescala.Common._
import purescala.DefOps._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Types._
import purescala.Expressions._
import purescala.Constructors.caseClassSelector

/** Represents a user-defined context-free grammar of expressions */
case class UserDefinedGrammar(ctx: LeonContext, program: Program, visibleFrom: Option[Definition], inputs: Seq[Identifier]) extends ExpressionGrammar {

  type Prod = ProductionRule[Label, Expr]

  val visibleDefs = visibleFrom match {
    case Some(d) =>
      visibleFunDefsFrom(d)(program)
    case None =>
      visibleFunDefsFromMain(program)
  }

  case class UserProduction(fd: FunDef, isTerminal: Boolean, isCommutative: Boolean, weight: Option[Int])

  val userProductions = visibleDefs.toSeq.sortBy(_.id).flatMap { fd =>
    val as = fd.extAnnotations

    val isTerminal   = as.contains("grammar.terminal")
    val isProduction = isTerminal || as.contains("grammar.production")

    if (isProduction) {
      val isCommut   = as.contains("grammar.commutative")
      val oweight    = as.get("grammar.weight").map(_(0).get.asInstanceOf[Int])

      Some(UserProduction(fd, isTerminal, isCommut, oweight))
    } else {
      None
    }
  }


  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[Label, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[Label], builder: (Seq[Expr] => Expr), tag: Tags.Tag = Tags.Top, cost: Int = 1) = {
    ProductionRule[Label, Expr](subs, builder, tag, cost)
  }

  def tpeToLabel(tpe: TypeTree): Label = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Label(ct.fieldsTypes.head).withAspect(Named(ct.classDef.id.name))

      case _ =>
        Label(tpe)
    }
  }

  def labelType(tpe: TypeTree): Option[TypeTree] = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Some(ct.fieldsTypes.head)

      case _ =>
        None
    }
  }

  def unwrapLabels(e: Expr, m: Map[Identifier, Identifier]): Expr = {
    preMap ({
      case CaseClass(cct, Seq(arg)) if cct.classDef.annotations("grammar.label") =>
        Some(arg)

      case CaseClassSelector(cct, v: Variable, id) if cct.classDef.annotations("grammar.label") =>
        m.get(v.id).map(_.toVariable)

      case _ =>
        None
    }, applyRec = true)(e)
  }

  val productions: Map[Label, Seq[Prod]] = {
    userProductions.flatMap { case UserProduction(fd, isTerm, isCommut, _) =>
      val lab = tpeToLabel(fd.returnType)

      val tag = if (isCommut) {
        Tags.Commut
      } else {
        Tags.Top
      }

      if (isTerm) {
        // if the function has one argument, we look for an input to p of the same name

        fd.params match {
          case Nil =>
            val expr = unwrapLabels(fd.body.get, Map())

            Some(lab -> terminal(expr, tag))

          case Seq(param) =>
            inputs.find(_.name == param.id.name) match {
              case Some(a) =>
                val expr = unwrapLabels(a.toVariable, Map())

                Some(lab -> terminal(expr, tag))
              case _ =>
                None
            }

          case _ =>
            None
        }
      } else {
        val subs = fd.params.map(p => tpeToLabel(p.getType))

        val m = fd.params.flatMap(p =>
          labelType(p.id.getType).map { tpe =>
            p.id -> FreshIdentifier("p", tpe)
          }
        ).toMap

        val holes = fd.params.map(p => m.getOrElse(p.id, p.id))

        val body = unwrapLabels(fd.body.get, m)

        Some(lab -> nonTerminal(subs, { sexprs => replaceFromIDs((holes zip sexprs).toMap, body) }, tag))
      }
    }.groupBy(_._1).mapValues(_.map(_._2))
  }

  def computeProductions(lab: Label)(implicit ctx: LeonContext) = {
    val lab2 = lab.copy(aspects = lab.aspects.filter {
      case _: Named => true
      case _ => false
    })

    productions.getOrElse(lab2, Nil)
  }
}
