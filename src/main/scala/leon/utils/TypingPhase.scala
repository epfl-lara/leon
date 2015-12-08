/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package utils

import purescala.Common._
import purescala.ExprOps.preTraversal
import purescala.Types._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Constructors._

object TypingPhase extends SimpleLeonPhase[Program, Program] {

  val name = "Typing"
  val description = "Ensure and enforce certain Leon typing rules"

  /**
   * This phase does 4 different things:
   *
   * 1) Ensure that functions that take and/or return a specific ADT subtype
   *    have this encoded explicitly in pre/postconditions. Solvers such as Z3
   *    unify types, which means that we need to ensure models are consistent
   *    with the original type constraints.
   *
   * 2) Report warnings in case parts of the tree are not correctly typed
   *    (Untyped).
   * 
   * 3) Make sure that abstract classes have at least one descendant
   *
   * 4) Add ADT invariants to all ADTs whose fields are not the most general
   *    type. This relates to point 1) but extends the generalization to
   *    fields of arguments.
   */
  def apply(ctx: LeonContext, pgm: Program): Program = {

    def argumentTypeConditions(exprs: Seq[Expr]): Option[Expr] = {
      val conds = exprs.flatMap(expr => expr.getType match {
        case cct: ClassType if cct.parent.isDefined =>
          Seq(IsInstanceOf(expr, cct))
        case at: ArrayType =>
          Seq(GreaterEquals(ArrayLength(expr), IntLiteral(0)))
        case _ =>
          Seq()
      })

      conds match {
        case Nil => None
        case xs => Some(andJoin(xs))
      }
    }

    pgm.definedFunctions.foreach(fd => {

      // Part (1)
      fd.precondition = {
        (fd.precondition ++ argumentTypeConditions(fd.params.map(_.toVariable))) match {
          case Nil => None
          case xs => Some(andJoin(xs.toSeq))
        }
      }

      fd.postcondition = fd.returnType match {
        case ct: ClassType if ct.parent.isDefined => {
          val resId = FreshIdentifier("res", ct)
          fd.postcondition match {
            case Some(p) =>
              Some(Lambda(Seq(ValDef(resId)), and(
                application(p, Seq(Variable(resId))),
                IsInstanceOf(Variable(resId), ct)
              ).setPos(p)).setPos(p))

            case None =>
              val pos = fd.body.map{ _.getPos } match {
                case Some(df: DefinedPosition) => df.focusEnd
                case _ => NoPosition
              }
              Some(Lambda(Seq(ValDef(resId)), IsInstanceOf(Variable(resId), ct)).setPos(pos))
          }
        }
        case _ => fd.postcondition
      }

      // Part (2)
      fd.body.foreach {
        preTraversal{
          case t if !t.isTyped =>
            ctx.reporter.warning(t.getPos, "Tree "+t.asString(ctx)+" is not properly typed ("+t.getPos.fullString+")")
          case _ =>
        }
      }
    })

    // Part (3)
    pgm.definedClasses.foreach {
      case acd: AbstractClassDef =>
        if (acd.knownCCDescendants.isEmpty) {
          ctx.reporter.error(acd.getPos, "Class "+acd.id.asString(ctx)+" has no concrete descendant!")
        }

      case _ =>
    }

    // Part (4)
    val newUnits = for (u <- pgm.units) yield {
      var fdsOf : Map[String, FunDef] = Map.empty

      for (c <- u.definedClasses) c match {
        case ccd: CaseClassDef =>
          val cct = ccd.typed
          val thisId = FreshIdentifier("thiss", cct.root, true)
          val thisVar = if (cct != cct.root) AsInstanceOf(Variable(thisId), cct) else Variable(thisId)
          val exprs = ccd.fields.map(vd => CaseClassSelector(cct, thisVar, vd.id))

          argumentTypeConditions(exprs) match {
            case Some(prec) =>
              val cd = ccd.root
              val cond = if (cct != cct.root) implies(IsInstanceOf(Variable(thisId), cct), prec) else prec
              pgm.definedFunctions.filter(fd => fd.isInvariant && fd.methodOwner == Some(cd)).headOption match {
                case Some(fd) =>
                  fd.fullBody = and(fd.fullBody, cond)

                case None =>
                  val fd = new FunDef(FreshIdentifier("inv", BooleanType, true), ccd.tparams, Seq(ValDef(thisId)), BooleanType)
                  fd.addFlag(IsADTInvariant).addFlag(IsMethod(cd))
                  cd.addFlag(IsADTInvariant)

                  fd.fullBody = cond
                  fdsOf += cd.id.name -> fd
              }
            case None =>
          }
        case _ =>
      }

      val defs = u.defs.map {
        case md: ModuleDef if fdsOf contains md.id.name =>
          val fd = fdsOf(md.id.name)
          fdsOf -= md.id.name
          ModuleDef(md.id, md.defs :+ fd, false)
        case d => d
      }

      val newCompanions = for ((name, fd) <- fdsOf) yield {
        ModuleDef(FreshIdentifier(name), Seq(fd), false)
      }

      u.copy(defs = defs ++ newCompanions)
    }

    Program(newUnits)
  }

}

