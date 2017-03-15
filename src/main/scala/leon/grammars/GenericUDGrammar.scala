/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import aspects._

import purescala.Common._
import purescala.DefOps._
import purescala.ExprOps._
import purescala.TypeOps.{instantiateType, instantiation_>:}
import purescala.Definitions._
import purescala.Types._
import purescala.Expressions._

import synthesis.{SynthesisContext, FunctionCallsFinder}

import scala.collection.mutable.ArrayBuffer

object GenericUDGrammar {
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
    "commut" -> Commut,
    "ite" -> ITE
  )
}

/** Represents a user-defined context-free grammar of expressions */
case class GenericUDGrammar(program: Program, visibleFrom: Option[Definition], inputs: Seq[Identifier]) extends ExpressionGrammar {
  import Tags._
  import GenericUDGrammar._

  def generateProductions(implicit ctx: LeonContext) = {
    val visibleDefs = visibleFrom match {
      case Some(d) =>
        visibleFunDefsFrom(d)(program)
      case None =>
        visibleFunDefsFromMain(program)
    }

    val fdInfos = visibleDefs.toSeq.sortBy(_.id).flatMap { fd =>

      val as = fd.extAnnotations

      val isProduction = as.contains("grammar.production")

      if (isProduction) {
        val cost = as("grammar.production").head.getOrElse(1).asInstanceOf[Int]
        val tag = (for {
          t <- as.get("grammar.tag")
          t2 <- t.headOption
          t3 <- t2
          t4 <- tags.get(t3.asInstanceOf[String])
        } yield t4).getOrElse(Top)

        List((fd, tag, cost))
      } else {
        Nil
      }
    }

    val productions = new ArrayBuffer[GenericProd]()

    for ((fd, tag, cost) <- fdInfos) {
      val expr = fd.fullBody
      val exprType = expr.getType

      val freeTps = fd.tparams.map(_.tp)

      expr match {
        // Special built-in "variable" case, which tells us how often to
        // generate variables of specific type
        case FunctionInvocation(TypedFunDef(fd, Seq(tp)), Seq()) if program.library.variable contains fd =>
          val inputGroups = inputs.groupBy(_.getType).toSeq

          for ((tpe, inputs) <- inputGroups) {
            instantiation_>:(exprType, tpe) match {
              case Some(tmap0) =>
                val size = inputs.size

                for (i <- inputs) {
                  productions += terminal(tpeToLabel(tpe), i.toVariable, tag, Math.max(1, cost/size), -1.0)
                }

              case _ =>
            }
          }

        // Special built-in "closure" case, which tells us how often to
        // generate closures of a specific type
        case FunctionInvocation(TypedFunDef(fdc, Seq(ft @ FunctionType(froms, to))), Seq()) if program.library.closure contains fdc =>

          val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>
            val lab = tpeToLabel(instantiateType(ft, tmap))

            val args = froms.zipWithIndex.map { case (tpe, i) =>
              ValDef(FreshIdentifier("a"+i, instantiateType(tpe, tmap)))
            }

            val rlab = tpeToLabel(instantiateType(to, tmap)).withAspect(aspects.ExtraTerminals(args.map(_.toVariable).toSet))

            ProductionRule[Label, Expr](Seq(rlab), { case Seq(body) =>
              Lambda(args, body)
            }, tag, cost, -1.0)
          }

          productions += GenericProd(fd.tparams, tpeToLabel(ft), Seq(to), prodBuilder)

        case _ =>
          if (freeTps.isEmpty) {
            val replacer = variableReplacer(expr, fd.params.map(_.id))

            val subs  = fd.params.map {
              p => tpeToLabel(p.getType)
            }

            productions += nonTerminal(tpeToLabel(fd.returnType), subs, { sexprs => 
              replacer(sexprs)
            }, tag, cost, -1.0)
          } else {
            val retType = fd.fullBody.getType

            val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>

              val m = fd.params.flatMap { p =>
                val ptype = instantiateType(p.id.getType, tmap)

                unwrapType(ptype).map { tpe =>
                  p.id -> FreshIdentifier("p", tpe)
                }
              }.toMap

              val expr = unwrapLabels(fd.fullBody, m)

              val holes = fd.params.map(p => m.getOrElse(p.id, p.id))

              val subs  = fd.params.map {
                p => tpeToLabel(instantiateType(p.getType, tmap))
              }

              val replacer = variableReplacer(expr, holes)

              ProductionRule[Label, Expr](subs, { sexprs => instantiateType(replacer(sexprs), tmap, m) }, tag, cost, -1.0)
            }

            productions += GenericProd(fd.tparams, tpeToLabel(retType), fd.params.map(_.getType), prodBuilder)
          }
      }
    }

    productions
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
}
