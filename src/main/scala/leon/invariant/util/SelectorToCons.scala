package leon
package invariant.util

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import solvers._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }
import ExpressionTransformer._
import TVarFactory._

object SelectToCons {
  // temporaries generated during conversion of field selects to ADT constructions
  val fieldSelContext = newContext
}

/**
 * A class that converts case-class or tuple selectors in an expression
 * to constructors, and updates a given lazy model.
 * We assume that all the arguments are flattened in the input expression.
 */
class SelectorToCons {

  import SelectToCons._

  var fldIdMap = Map[Identifier, (Variable, Int)]()

  /**
   * For now this works only on a disjunct
   */
  def selToCons(disjunct: Seq[Expr]): Seq[Expr] = {
    def classSelToCons(eq: Equals) = eq match {
      case Equals(r: Variable, CaseClassSelector(ctype, cc: Variable, selfld)) =>
        //convert this to a cons by creating dummy variables
        val args = ctype.fields.zipWithIndex.map {
          case (fld, i) if fld.id == selfld => r
          case (fld, i) =>
            val t = createTemp("fld", fld.getType, fieldSelContext) //create a dummy identifier there
            fldIdMap += (t -> (cc, i))
            t.toVariable
        }
        Equals(cc, CaseClass(ctype, args))
      case _ =>
        throw new IllegalStateException("Selector not flattened: " + eq)
    }
    def tupleSelToCons(eq: Equals) = eq match {
      case Equals(r: Variable, TupleSelect(tp: Variable, idx)) =>
        val tupleType = tp.getType.asInstanceOf[TupleType]
        //convert this to a Tuple by creating dummy variables
        val args = (1 until tupleType.dimension + 1).map { i =>
          if (i == idx) r
          else {
            val t = createTemp("fld", tupleType.bases(i - 1), fieldSelContext) //note: we have to use i-1
            fldIdMap += (t -> (tp, i - 1))
            t.toVariable
          }
        }
        Equals(tp, Tuple(args))
      case _ =>
        throw new IllegalStateException("Selector not flattened: " + eq)
    }
    //println("Input expression: "+ine)
    disjunct.map { // we need to traverse top-down
      case eq @ Equals(_, _: CaseClassSelector) =>
        classSelToCons(eq)
      case eq @ Equals(_, _: TupleSelect) =>
        tupleSelToCons(eq)
      case _: CaseClassSelector | _: TupleSelect =>
        throw new IllegalStateException("Selector not flattened")
      case e => e
    }
//    println("Output expression: "+rese)
//    rese
  }

  //  def tupleSelToCons(e: Expr): Expr = {
  //    val (r, tpvar, index) = e match {
  //      case Equals(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
  //      // case Iff(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
  //      case _ => throw new IllegalStateException("Not a tuple-selector call")
  //    }
  //    //convert this to a Tuple by creating dummy variables
  //    val tupleType = tpvar.getType.asInstanceOf[TupleType]
  //    val args = (1 until tupleType.dimension + 1).map((i) => {
  //      if (i == index) r
  //      else {
  //        //create a dummy identifier there (note that here we have to use i-1)
  //        createTemp("fld", tupleType.bases(i - 1), fieldSelContext).toVariable
  //      }
  //    })
  //    Equals(tpvar, Tuple(args))
  //  }

  /**
   * Expands a given model into a model with mappings for identifiers introduced during flattening.
   * Note: this class cannot be accessed in parallel.
   */
  def getModel(initModel: LazyModel) = new LazyModel {
    override def get(iden: Identifier) = {
      val idv = initModel.get(iden)
      if (idv.isDefined) idv
      else {
        fldIdMap.get(iden) match {
          case Some((Variable(inst), fldIdx)) =>
            initModel(inst) match {
              case CaseClass(_, args) => Some(args(fldIdx))
              case Tuple(args)        => Some(args(fldIdx))
            }
          case None => None
        }
      }
    }
  }
}