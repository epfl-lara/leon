package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

trait Z3ModelReconstruction {
  self: AbstractZ3Solver =>

  // exprToZ3Id, softFromZ3Formula, reporter

  private final val AUTOCOMPLETEMODELS : Boolean = true
  private final val SIMPLESTCOMPLETION : Boolean = true // if true, use 0, Nil(), etc., else random

  def modelValue(model: Z3Model, id: Identifier, tpe: TypeTree = null) : Option[Expr] = {
    val expectedType = if(tpe == null) id.getType else tpe
    
    if(!exprToZ3Id.isDefinedAt(id.toVariable)) None else {
      val z3ID : Z3AST = exprToZ3Id(id.toVariable)

      expectedType match {
        case BooleanType => model.evalAs[Boolean](z3ID).map(BooleanLiteral(_))
        case Int32Type => model.evalAs[Int](z3ID).map(IntLiteral(_))
        case MapType(kt,vt) => model.eval(z3ID) match {
          case None => None
          case Some(t) => model.getArrayValue(t) match {
            case None => None
            case Some((map, elseValue)) => 
              // assert(elseValue == mapRangeNoneConstructors(vt)())
              val singletons = for ((index, value) <- map if (z3.getASTKind(value) match {
                case Z3AppAST(someCons, _) if someCons == mapRangeSomeConstructors(vt) => true
                case _ => false
              })) yield {
                z3.getASTKind(value) match {
                  case Z3AppAST(someCons, arg :: Nil) if someCons == mapRangeSomeConstructors(vt) => SingletonMap(fromZ3Formula(index), fromZ3Formula(arg))
                  case _ => scala.sys.error("unexpected value in map: " + value)
                }
              }
              if (singletons.isEmpty) Some(EmptyMap(kt, vt)) else Some(FiniteMap(singletons.toSeq))
          }
        }
        case other => model.eval(z3ID) match {
          case None => None
          case Some(t) => softFromZ3Formula(t)
        }
      }
    }
  }

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
