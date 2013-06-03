/* Copyright 2009-2013 EPFL, Lausanne */

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
  private final val SIMPLESTCOMPLETION : Boolean = true // if true, use 0, Nil(), etc., else random

  def modelValue(model: Z3Model, id: Identifier, tpe: TypeTree = null) : Option[Expr] = {
    val expectedType = if(tpe == null) id.getType else tpe
    
    if(exprToZ3Id.isDefinedAt(id.toVariable)) {
      val z3ID : Z3AST = exprToZ3Id(id.toVariable)

      expectedType match {
        case BooleanType => model.evalAs[Boolean](z3ID).map(BooleanLiteral(_))
        case Int32Type => model.evalAs[Int](z3ID).map(IntLiteral(_))
        case other => model.eval(z3ID) match {
          case None => None
          case Some(t) => softFromZ3Formula(model, t, expectedType)
        }
      }
    } else None
  }

  // def modelValue(model: Z3Model, id: Identifier, tpe: TypeTree = null) : Option[Expr] = {
  //   val expectedType = if(tpe == null) id.getType else tpe
  //   
  //   if(exprToZ3Id.isDefinedAt(id.toVariable)) {
  //     val z3ID : Z3AST = exprToZ3Id(id.toVariable)


  //     rec(z3ID, expectedType)
  //   } else None
  // }

  def modelToMap(model: Z3Model, ids: Iterable[Identifier]) : Map[Identifier,Expr] = {
    var asMap = Map.empty[Identifier,Expr]

    def completeID(id : Identifier) : Unit = if (SIMPLESTCOMPLETION) {
      asMap = asMap + ((id -> simplestValue(id.toVariable)))
      reporter.info("Completing variable '" + id + "' to simplest value")
    } else {
      asMap = asMap + ((id -> randomValue(id.toVariable)))
      reporter.info("Completing variable '" + id + "' to random value")
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
