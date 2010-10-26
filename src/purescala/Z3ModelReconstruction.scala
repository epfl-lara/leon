package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

trait Z3ModelReconstruction {
  self: Z3Solver =>

  def modelValue(model: Z3Model, id: Identifier, tpe: TypeTree = null) : Option[Expr] = {
    val expectedType = if(tpe == null) id.getType else tpe
    
    if(!id2idMap.isDefinedAt(id.uniqueName)) None else {
      val z3ID : Z3AST = id2idMap(id.uniqueName)

      expectedType match {
        case BooleanType => model.evalAsBool(z3ID).map(BooleanLiteral(_))
        case Int32Type => model.evalAsInt(z3ID).map(IntLiteral(_))
        case _ => None
      }
    }
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
