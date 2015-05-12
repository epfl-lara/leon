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
import invariant.util.Util._
import invariant.util.ExpressionTransformer._
import invariant.structure.FunctionUtils._
import invariant.util.LetTupleSimplification._

/**
 * A simplifier phase that eliminates tuples that are not needed
 * from function bodies, and also performs other simplifications.
 * Note: performing simplifications during instrumentation
 * will affect the validity of the information stored in function info.
 */
object ProgramSimplifier {
  val debugSimplify = false

  def mapProgram(funMap: Map[FunDef, FunDef]): Map[FunDef, FunDef] = {

    def mapExpr(ine: Expr): Expr = {
      val replaced = simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
          FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
        case _ => e
      })(ine)

      // One might want to add the maximum function to the program in the stack
      // and depth instrumentation phases if inlineMax is removed from here
      val allSimplifications =
        simplifyTuples _ andThen
          simplifyMax _ andThen
          simplifyLetsAndLetsWithTuples _ andThen
          simplifyAdditionsAndMax _ andThen
          inlineMax _

      allSimplifications(replaced)
    }

    for ((from, to) <- funMap) {
      to.fullBody = mapExpr(from.fullBody)
      //copy annotations
      from.flags.foreach(to.addFlag(_))
    }
    funMap
  }

  def createNewFunDefs(program: Program): Map[FunDef, FunDef] = {
    val allFuncs = functionsWOFields(program.definedFunctions)

    allFuncs.foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) if fd.isTheoryOperation =>
        accMap + (fd -> fd)
      case (accMap, fd) => {
        //here we need not augment the return types
        val freshId = FreshIdentifier(fd.id.name, fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.returnType, fd.params)
        accMap.updated(fd, newfd)
      }
    }
  }

  def createNewProg(mappedFuncs: Map[FunDef, FunDef], prog: Program): Program = {
    val newprog = copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if mappedFuncs.contains(fd) =>
        mappedFuncs(fd)
      case d => d
    })

    if (debugSimplify)
      println("After Simplifications: \n" + ScalaPrinter.apply(newprog))
    newprog
  }

  def apply(program: Program): Program = {
    val newFuncs = createNewFunDefs(program)
    val mappedFuncs = mapProgram(newFuncs)
    createNewProg(mappedFuncs, program)
  }
}