/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import invariant.util.ExpressionTransformer._
import invariant.structure.FunctionUtils._
import invariant.util.LetTupleSimplification._

object RunnableCodePhase extends TransformationPhase {

  val name = "Runnable Code"
  val description = "Generating Scala runnable code from the instrumented code"

  def apply(ctx: LeonContext, pgm: Program): Program = {
    val debugRunnable = false

    val funMap = (pgm.definedFunctions.distinct).foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) => {
        val freshId = FreshIdentifier((fd.id.name).replaceAll("-",""), fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        accMap + (fd -> newfd)
      }
    }

    def removeContracts(ine: Expr, fd: FunDef): Expr = simplePostTransform({
        case Ensuring(body, pred) => removeContracts(body, fd)
        case Require(pred, body) => removeContracts(body, fd)
        case e => e
    })(ine)

    for ((from, to) <- funMap) {
      to.fullBody = removeContracts(from.fullBody, from)
      from.flags.foreach(to.addFlag(_)) //copy annotations
    }
    val newprog = copyProgram(pgm, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if funMap.contains(fd) => funMap(fd)
      case d                                 => d
    })

    if (debugRunnable)
      println("After transforming to runnable code: \n" + ScalaPrinter.apply(newprog))
    newprog
  }
}
