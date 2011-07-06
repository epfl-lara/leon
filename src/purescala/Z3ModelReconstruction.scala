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
    
    if(exprToZ3Id.isDefinedAt(id.toVariable)) {
      val z3ID : Z3AST = exprToZ3Id(id.toVariable)

      def rec(ast: Z3AST, expTpe: TypeTree): Option[Expr] = expTpe match {
        case BooleanType => model.evalAs[Boolean](ast).map(BooleanLiteral(_))
        case Int32Type => model.evalAs[Int](ast).map(IntLiteral(_))
        case MapType(kt,vt) => model.eval(ast) match {
          case None => None
          case Some(t) => model.getArrayValue(t) match {
            case None => None
            case Some((map, elseValue)) => 
              val singletons = map.map(e => (e, z3.getASTKind(e._2))).collect {
                case ((index, value), Z3AppAST(someCons, arg :: Nil)) if someCons == mapRangeSomeConstructors(vt) => SingletonMap(rec(index, kt).get, rec(arg, vt).get)
              }
              (if (singletons.isEmpty) Some(EmptyMap(kt, vt)) else Some(FiniteMap(singletons.toSeq))).map(_.setType(expTpe))
          }
        }
        case funType @ FunctionType(fts, tt) => model.eval(ast) match {
          case None => None
          case Some(t) => model.getArrayValue(t) match {
            case None => None
            case Some((es, ev)) =>
              val entries: Seq[(Seq[Expr], Expr)] = es.toSeq.map(e => (e, z3.getASTKind(e._1))).collect {
                case ((key, value), Z3AppAST(cons, args)) if cons == funDomainConstructors(funType) => ((args zip fts) map (p => rec(p._1, p._2).get), rec(value, tt).get)
              }
              val elseValue = rec(ev, tt).get
              Some(AnonymousFunction(entries, elseValue).setType(expTpe))
          }
        }
        case SetType(dt) => model.eval(ast) match {
          case None => None
          case Some(t) => model.getSetValue(t) match {
            case None => None
            case Some(set) => {
              val elems = set.map(e => rec(e, dt).get)
              (if (elems.isEmpty) Some(EmptySet(dt)) else Some(FiniteSet(elems.toSeq))).map(_.setType(expTpe))
            }
          }
        }
        case other => model.eval(ast) match {
          case None => None
          case Some(t) => softFromZ3Formula(t)
        }
      }

      rec(z3ID, expectedType)
    } else None
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
