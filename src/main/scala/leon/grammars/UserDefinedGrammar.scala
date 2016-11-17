/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import aspects._

import purescala.Common._
import purescala.DefOps._
import purescala.ExprOps._
import purescala.TypeOps.{instantiateType, instantiation_<:, unify}
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
      val weight = as("grammar.production").head.getOrElse(1).asInstanceOf[Int]
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

  def unwrapType(tpe: TypeTree): Option[TypeTree] = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Some(ct.fieldsTypes.head)

      case _ =>
        None
    }
  }

  def tpeToLabel(tpe: TypeTree): Label = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Label(unwrapType(tpe).get).withAspect(RealTyped(ct))

      case _ =>
        Label(tpe)
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

  def instantiateProductions(tpe: TypeTree, ps: Seq[UserProduction]): Seq[Prod] = {
    val lab = tpeToLabel(tpe)

    ps.flatMap { case UserProduction(fd, tag, w) =>
      instantiation_<:(fd.returnType, tpe) match {
        case Some(tmap0) =>

          val free = fd.tparams.map(_.tp) diff tmap0.keySet.toSeq;

          val tmaps = if (free.nonEmpty) {
            // Instantiate type parameters not constrained by the return value
            // of `fd`
            //
            // e.g.:
            // def countFilter[T](x: List[T], y: T => Boolean): BigInt
            //
            // We try to find instantiation of T such that arguments have
            // candidates
            //

            // Step 1. We identify the type patterns we need to match:
            // e.g. (List[T], T => Boolean)
            val pattern0 = fd.params.map(_.getType).distinct

            // Step 2. We collect a set of interesting types that we can use to
            // fill our pattern
            val types = (userProductions.collect {
              case UserProduction(fd, _, _) if fd.tparams.isEmpty => fd.returnType
            } ++ inputs.map(_.getType)).toSet

            def discover(free: TypeParameter, fixed: Set[Map[TypeParameter, TypeTree]]): Set[Map[TypeParameter, TypeTree]] = {
              for {
                map0 <- fixed
                p1 = pattern0.map(instantiateType(_, map0))
                p <- p1
                t <- types
                map1 <- unify(p, t, Seq(free))
              } yield {
                map0 ++ map1
              }
            }

            var tmaps = Set(tmap0)

            for (f <- free) {
              tmaps = discover(f, tmaps)
            }

            tmaps
          } else {
            List(tmap0)
          }

          (for (tmap <- tmaps) yield {
            val m = fd.params.flatMap { p =>
              val ptype = instantiateType(p.id.getType, tmap)

              unwrapType(ptype).map { tpe =>
                p.id -> FreshIdentifier("p", tpe)
              }
            }.toMap


            val expr = unwrapLabels(fd.fullBody, m)

            if (fd.params.isEmpty) {
              expr match {
                // Special built-in "variable" case, which tells us how often to
                // generate variables of specific type
                case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.variable contains fd =>

                  val targetType = instantiateType(tp, tmap)
                  val vars = inputs.filter (_.getType == targetType)

                  val size = vars.size.toDouble
                  vars map (v => terminal(v.toVariable, classOf[Variable], tag, cost = 1, w/size))

                case _ =>
                  List(terminal(instantiateType(expr, tmap, Map()), classOf[Expr], tag, cost = 1, w))
              }
            } else {

              val holes = fd.params.map(p => m.getOrElse(p.id, p.id))
              val subs  = fd.params.map {
                p => tpeToLabel(instantiateType(p.getType, tmap))
              }

              List(nonTerminal(subs, { sexprs => 
                val res = instantiateType(replaceFromIDs((holes zip sexprs).toMap, expr), tmap, m) 
                inlineTrivialities(res)
              }, classOf[Expr], tag, cost = 1, w))
            }
          }).flatten

        case None =>
          None
      }
    }
  }

  protected[grammars] def computeProductions(lab: Label)(implicit ctx: LeonContext) = {
    val realType = lab.aspects.collect {
      case RealTyped(tpe) => tpe
    }.headOption.getOrElse(lab.getType)

    val prods = instantiateProductions(realType, userProductions)

    val ws = prods map (_.weight)

    if (ws.nonEmpty) {
      val sum = ws.sum
      // log(prob) = log(weight/Σ(weights))
      val logProbs = ws.map(w => Math.log(w/sum))
      val maxLogProb = logProbs.max

      for ((p, logProb) <- prods zip logProbs) yield {
        // cost = normalized log prob.
        val cost = (logProb/maxLogProb).round.toInt
        p.copy(cost = cost, weight = logProb)
      }
    } else {
      Nil
    }
  }

}
