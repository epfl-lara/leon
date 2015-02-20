/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers.z3

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

trait Z3ModelReconstruction {
  self: AbstractZ3Solver =>

  // exprToZ3Id, softFromZ3Formula, reporter

  private final val AUTOCOMPLETEMODELS : Boolean = true

  def modelValue(model: Z3Model, id: Identifier, tpe: TypeTree = null) : Option[Expr] = {
    val expectedType = if(tpe == null) id.getType else tpe
    
    variables.getZ3(id.toVariable).flatMap { z3ID =>
      expectedType match {
        case BooleanType => model.evalAs[Boolean](z3ID).map(BooleanLiteral(_))
        case Int32Type =>
          model.evalAs[Int](z3ID).map(IntLiteral(_)).orElse{
            model.eval(z3ID).flatMap(t => softFromZ3Formula(model, t))
          }
        case IntegerType => model.evalAs[Int](z3ID).map(InfiniteIntegerLiteral(_))
        case other => model.eval(z3ID) match {
          case None => None
          case Some(t) => softFromZ3Formula(model, t)
        }
      }
    }
  }

  def modelToMap(model: Z3Model, ids: Iterable[Identifier]) : Map[Identifier,Expr] = {
    var asMap = Map.empty[Identifier,Expr]

    def completeID(id : Identifier) : Unit = {
      asMap = asMap + ((id -> simplestValue(id.getType)))
      reporter.debug("Completing variable '" + id + "' to simplest value")
    }

    for(id <- ids) {
      modelValue(model, id) match {
        case None if (AUTOCOMPLETEMODELS) => completeID(id)
        case None => ;
        case Some(v @ Variable(exprId)) if (AUTOCOMPLETEMODELS && exprId == id) => completeID(id)
        case Some(ex) => asMap = asMap + ((id -> ex))
      }
    }
    asMap
  }

  def printExtractedModel(model: Z3Model, ids : Iterable[Identifier]) : Unit = {
    reporter.info("Tentative extracted model")
    reporter.info("*************************")
    for(id <- ids) {
      val strRep = modelValue(model, id) match {
        case Some(e) => e.toString
        case None => "??"
      }
      reporter.info(id + "       ->     " + strRep)
    }
  }
}
