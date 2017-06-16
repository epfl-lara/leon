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
case class GenericUDGrammar(program: Program, visibleFrom: Option[Definition], inputs: Seq[Expr]) extends ExpressionGrammar {
  import Tags._
  import GenericUDGrammar._

  def generateProductions(implicit ctx: LeonContext) = ctx.timers.grammars.generic.timed {

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

    val productions = new ArrayBuffer[GenericProdSeed]()

    for ((fd, tag, cost) <- fdInfos) {
      // Remove asserts that come from divisions
      val expr = postMap {
        case Assert(_, _, b) => Some(b)
        case _ => None
      }(fd.fullBody)

      val exprType = fd.returnType

      val freeTps = fd.tparams.map(_.tp)

      val unwrappedParams = fd.paramIds.map( id =>
        id -> (unwrapType(id.getType) match {
          case Some(tp) => FreshIdentifier(id.name, tp, true)
          case None => id
        })
      ).toMap

      unwrapLabels(expr, unwrappedParams) match {
        // Special built-in "variable" case, which tells us how often to
        // generate variables of specific type.
        // We additionally count as "variables" hard-coded hints by the synthesizer
        case FunctionInvocation(TypedFunDef(fd, Seq(_)), Seq()) if program.library.variable contains fd =>
          val inputGroups = inputs.groupBy(_.getType).toSeq

          for ((tpe, inputs) <- inputGroups) {
            instantiation_>:(unwrapOrReturnType(exprType), tpe) match {
              case Some(map) =>
                val size = inputs.size

                for (in <- inputs) {
                  productions += terminal(tpeToLabel(instantiateType(exprType, map)), in, tag, Math.max(1, cost / size), -1.0)
                }
              case None =>

            }
          }

        // Special built-in "closure" case, which tells us how often to
        // generate closures of a specific type
        case FunctionInvocation(TypedFunDef(fdc, Seq(ft @ FunctionType(froms, to))), Seq())
            if program.library.closure contains fdc =>

          val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>
            val args = froms.zipWithIndex.map { case (tpe, i) =>
              ValDef(FreshIdentifier("a"+i, instantiateType(tpe, tmap)))
            }

            val rlab = tpeToLabel(instantiateType(to, tmap)).withAspect(aspects.ExtraTerminals(args.map(_.toVariable).toSet))

            ProductionRule[Label, Expr](Seq(rlab), { case Seq(body) =>
              Lambda(args, body)
            }, tag, cost, -1.0)
          }

          productions += GenericProdSeed(fd.tparams, tpeToLabel(ft), Seq(to), prodBuilder)

        case _ =>
          if (freeTps.isEmpty) {
            val unwrapped = unwrapLabels(expr, unwrappedParams)
            val replacer = variableReplacer(unwrapped, fd.paramIds.map(unwrappedParams))

            val subs  = fd.params.map { p => tpeToLabel(p.getType) }

            productions += nonTerminal(tpeToLabel(fd.returnType), subs, replacer, tag, cost, -1.0)
          } else {
            val retType = fd.returnType

            val prodBuilder = { (tmap: Map[TypeParameter, TypeTree]) =>

              val m = fd.params.flatMap { p =>
                val ptype = instantiateType(p.id.getType, tmap)

                unwrapType(ptype).map { tpe =>
                  p.id -> FreshIdentifier("p", tpe)
                }
              }.toMap

              val unwrapped = unwrapLabels(fd.fullBody, m)
              //println(s"Original: ${fd.fullBody}")
              //println(s"Unwrapped: $unwrapped")

              val holes = fd.params.map(p => m.getOrElse(p.id, p.id))

              val subs  = fd.params.map {
                p => tpeToLabel(instantiateType(p.getType, tmap))
              }

              val replacer = variableReplacer(unwrapped, holes)

              ProductionRule[Label, Expr](subs, { sexprs => instantiateType(replacer(sexprs), tmap, m) }, tag, cost, -1.0)
            }

            productions += GenericProdSeed(fd.tparams, tpeToLabel(retType), fd.params.map(_.getType), prodBuilder)
          }
      }
    }
    //productions foreach (p => println(f"${Console.BOLD}${p.label.asString}%50s${Console.RESET} ::= " + genProdAsString(p)))

    productions
  }

  def unwrapOrReturnType(tpe: TypeTree): TypeTree = {
    unwrapType(tpe).getOrElse(tpe)
  }

  // Removes labels from a type to make it a normal Leon type
  def unwrapType(tpe: TypeTree): Option[TypeTree] = {
    tpe match {
      case ct: ClassType if ct.classDef.annotations("grammar.label") && ct.fields.size == 1 =>
        Some(ct.fieldsTypes.head)

      case _ =>
        None
    }
  }

  def tpeToLabel(tpe: TypeTree): Label = {
    unwrapType(tpe) match {
      case Some(underlying) =>
        val within = {
          val cname = tpe.asInstanceOf[ClassType].classDef.id.name
          val chunks = cname.split("_")
          if (chunks.last == "None") // TODO FIXME!!!
            None
          else Some((chunks.last, chunks.init.last.toInt))
        }
        Label(underlying).withAspect(RealTyped(within))
      case None =>
        Label(tpe)
    }
  }

  // Unwraps labelled subexpressions which indicate predicated types to the normal Leon values.
  // E.g. BigInt_0_Minus(x) becomes x.
  // m is a map from variables of labeled types to variables of normal types
  def unwrapLabels(e: Expr, m: Map[Identifier, Identifier]): Expr = {
    preMap ({
      case CaseClass(cct, Seq(arg)) if cct.classDef.annotations("grammar.label") =>
        Some(arg)

      case CaseClassSelector(cct, v: Variable, _) if cct.classDef.annotations("grammar.label") =>
        m.get(v.id).map(_.toVariable)

      case _ =>
        None
    }, applyRec = true)(e)
  }
}
