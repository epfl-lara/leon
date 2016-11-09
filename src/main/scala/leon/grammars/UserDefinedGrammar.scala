/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import aspects._

import purescala.Common._
import purescala.DefOps._
import purescala.ExprOps._
import purescala.Definitions._
import purescala.Types._
import purescala.Expressions._

import synthesis.SynthesisContext

object UserDefinedGrammar {
  import Tags._
  def tags = Map(
    "top" -> Top,
    "0" -> Zero,
    "1" -> One,
    "booleanC" -> BooleanC,
    "const" -> Constant,
    "and" -> And,
    "or" -> Or,
    "not" -> Not,
    "plus" -> Plus,
    "minus" -> Minus,
    "times" -> Times,
    "mod" -> Mod,
    "div" -> Div,
    "equals" -> Equals,
    "commut" -> Commut
  )
}

/** Represents a user-defined context-free grammar of expressions */
case class UserDefinedGrammar(sctx: SynthesisContext, program: Program, visibleFrom: Option[Definition], inputs: Seq[Identifier]) extends ExpressionGrammar {
  import Tags._
  import UserDefinedGrammar._
  type Prod = ProductionRule[Label, Expr]

  val visibleDefs = visibleFrom match {
    case Some(d) =>
      visibleFunDefsFrom(d)(program)
    case None =>
      visibleFunDefsFromMain(program)
  }

  case class UserProduction(fd: FunDef, tag: Tag, weight: Int)

  val userProductions = visibleDefs.toSeq.sortBy(_.id).flatMap { fd =>
    val as = fd.extAnnotations

    val isProduction = as.contains("grammar.production")

    if (isProduction) {
      val weight   = as("grammar.production").head.getOrElse(1).asInstanceOf[Int]
      val tag = (for {
        t <- as.get("grammar.tag")
        t2 <- t.headOption
        t3 <- t2
        t4 <- tags.get(t3.asInstanceOf[String])
      } yield t4).getOrElse(Top)

      Some(UserProduction(fd, tag, weight))
    } else {
      None
    }
  }


  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(builder: => Expr, outType: Class[_ <: Expr], tag: Tags.Tag = Tags.Top, cost: Int, weight: Double) = {
    ProductionRule[Label, Expr](Nil, _ => builder, outType, tag, cost, weight)
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(subs: Seq[Label], builder: (Seq[Expr] => Expr), outType: Class[_ <: Expr], tag: Tags.Tag = Tags.Top, cost: Int, weight: Double) = {
    ProductionRule[Label, Expr](subs, builder, outType, tag, cost, weight)
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
    val ps = userProductions.flatMap { case UserProduction(fd, tag, w) =>
      val lab = tpeToLabel(fd.returnType)

      val isTerm = fd.params.isEmpty

      if (isTerm) {
        // if the function has one argument, we look for an input to p of the same name

        fd.fullBody match {
          // Special built-in "variable" case, which tells us how often to generate variables of specific type
          case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.variable contains fd =>
            val vars = inputs.filter(_.getType == tp)
            val size = vars.size.toDouble
            vars map (v => lab -> terminal(v.toVariable, classOf[Variable], tag, cost = 1, w/size))
          case _ =>
            val expr = unwrapLabels(fd.body.get, Map())
            Some(lab -> terminal(expr, expr.getClass, tag, cost = 1, w))
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

        Some(lab -> nonTerminal(subs,
                                sexprs => replaceFromIDs((holes zip sexprs).toMap, body),
                                body.getClass,
                                tag,
                                cost = 1,
                                w))
      }
    }.groupBy(_._1).mapValues(_.map(_._2))

    for ((l, pw) <- ps) yield {
      val ws = pw map (_.weight)

      val prods = if (ws.nonEmpty) {
        val sum = ws.sum
        // log(prob) = log(weight/Σ(weights))
        val logProbs = ws.map(w => Math.log(w/sum))
        val maxLogProb = logProbs.max

        for ((p, logProb) <- pw zip logProbs) yield {
          // cost = normalized log prob.
          val cost = (logProb/maxLogProb).round.toInt
          p.copy(cost = cost, weight = logProb)
        }
      } else {
        sys.error("Whoot???")
      }

      l -> prods
    }
  }

  protected def computeProductions(lab: Label)(implicit ctx: LeonContext) = {
    val lab2 = lab.copy(aspects = lab.aspects.filter {
      case _: Named => true
      case _ => false
    })
    productions.getOrElse(lab2, Nil)
  }

}
