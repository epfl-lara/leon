/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.TypeTrees._
import purescala.Trees._
import purescala.Definitions._

object SubtypingPhase extends LeonPhase[Program, Program] {

  val name = "Subtyping"
  val description = "Protection of function arguments with subtypes"

  //note that this will mutate the existing program functions and
  //not return a new different program
  def run(ctx: LeonContext)(pgm: Program): Program = {
    pgm.definedFunctions.foreach(fd => {

      fd.precondition = {
        val argTypesPreconditions = fd.args.flatMap(arg => arg.tpe match {
          case cct@CaseClassType(cd) => Seq(CaseClassInstanceOf(cd, arg.id.toVariable))
          case _ => Seq()
        })
        argTypesPreconditions match {
          case Nil => fd.precondition
          case xs => fd.precondition match {
            case Some(p) => Some(And(p +: xs))
            case None => Some(And(xs))
          }
        }
      }

      fd.postcondition = fd.returnType match {
        case cct@CaseClassType(cd) => {
          val subtypingConstraint = CaseClassInstanceOf(cd, ResultVariable())
          fd.postcondition match {
            case Some(p) => Some(And(subtypingConstraint, p))
            case None => Some(subtypingConstraint)
          }
        }
        case _ => fd.postcondition
      }

    })
    pgm
  }

}

