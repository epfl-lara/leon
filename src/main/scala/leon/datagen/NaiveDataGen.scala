/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package datagen

import purescala.Common._
import purescala.Expressions._
import purescala.Types._
import purescala.Definitions._
import purescala.Quantification._
import utils.StreamUtils._

import evaluators._

import scala.collection.mutable.{Map=>MutableMap}

/** Utility functions to generate values of a given type.
  * In fact, it could be used to generate *terms* of a given type,
  * e.g. by passing trees representing variables for the "bounds". */
@deprecated("Stream-based datagen is deprecated, use GrammarDataGen with ValueGrammar instead", "3.0")
class NaiveDataGen(ctx: LeonContext, p: Program, evaluator: Evaluator, _bounds : Option[Map[TypeTree,Seq[Expr]]] = None) extends DataGenerator {

  val bounds = _bounds.getOrElse(Map())

  private def tpStream(tp: TypeParameter, i: Int = 1): Stream[Expr] = Stream.cons(GenericValue(tp, i), tpStream(tp, i+1))

  private val streamCache : MutableMap[TypeTree,Stream[Expr]] = MutableMap.empty
  def generate(tpe : TypeTree) : Stream[Expr] = {
    try {
      streamCache.getOrElse(tpe, {
        val s = generate0(tpe)
        streamCache(tpe) = s
        s
      })
    } catch {
      case so: StackOverflowError =>
        Stream.empty
    }
  }

  private def generate0(tpe: TypeTree): Stream[Expr] = bounds.get(tpe).map(_.toStream).getOrElse {
    tpe match {
      case BooleanType =>
        BooleanLiteral(true) #:: BooleanLiteral(false) #:: Stream.empty

      case Int32Type =>
        IntLiteral(0) #:: IntLiteral(1) #:: IntLiteral(2) #:: IntLiteral(-1) #:: Stream.empty

      case tp: TypeParameter =>
        tpStream(tp)

      case TupleType(bses) =>
        cartesianProduct(bses.map(generate)).map(Tuple)

      case act : AbstractClassType =>
        // We prioritize base cases among the children.
        // Otherwise we run the risk of infinite recursion when
        // generating lists.
        val ccChildren = act.knownCCDescendants

        val (leafs,conss) = ccChildren.partition(_.fields.isEmpty)
        
        // FIXME: Will not work for mutually recursive types
        val sortedConss = conss sortBy { _.fields.count{ _.getType.isInstanceOf[ClassType]}}

        // The stream for leafs...
        val leafsStream = leafs.toStream.flatMap(generate)

        // ...to which we append the streams for constructors.
        leafsStream.append(interleave(sortedConss.map(generate)))

      case cct : CaseClassType =>
        if(cct.fields.isEmpty) {
          Stream.cons(CaseClass(cct, Nil), Stream.empty)
        } else {
          val fieldTypes = cct.fieldsTypes
          cartesianProduct(fieldTypes.map(generate)).map(CaseClass(cct, _))
        }

      case _ => Stream.empty
    }
  }

  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid : Int, maxEnumerated : Int) : Iterator[Seq[Expr]] = {
    val filtering = if (satisfying == BooleanLiteral(true)) {
      { (e: Seq[Expr]) => true }
    } else {
      evaluator.compile(satisfying, ins).map { evalFun =>
        val sat = EvaluationResults.Successful(BooleanLiteral(true))

        { (e: Seq[Expr]) => evalFun(new solvers.Model((ins zip e).toMap)) == sat }
      } getOrElse {
        { (e: Seq[Expr]) => false }
      }
    }

    cartesianProduct(ins.map(id => generate(id.getType)))
      .take(maxEnumerated)
      .takeWhile(s => !interrupted.get)
      .filter{filtering}
      .take(maxValid)
      .iterator
  }
}
