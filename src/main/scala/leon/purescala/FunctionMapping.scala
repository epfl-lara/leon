/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps._
import Types._

abstract class FunctionMapping extends TransformationPhase {
  
  val functionToFunction : Map[FunDef, FunctionTransformer]
  
  case class FunctionTransformer(
    to : FunDef,
    onArgs : Seq[Expr] => List[Expr],
    onTypes : Seq[TypeTree] => List[TypeTree]
  )
  
  val name = "Function Mapping"
  val description = "Replace functions and their invocations according to a given mapping"
  
  private def replaceCalls(e : Expr) : Expr = preMap {
    case fi@FunctionInvocation(TypedFunDef(fd, tps), args) if functionToFunction contains fd =>
      val FunctionTransformer(to, onArgs, onTypes) = functionToFunction(fd)
      Some(FunctionInvocation(TypedFunDef(to, onTypes(tps)), onArgs(args)).setPos(fi))
    // case MethodInvocation
    case _ => None
  }(e)

  def apply(ctx: LeonContext, program: Program): Program = {
    val newP = 
      program.copy(units = for (u <- program.units) yield {
        u.copy(
          defs = u.defs map {
            case m: ModuleDef =>
              m.copy(defs = for (df <- m.defs) yield {
                df match {
                  case f : FunDef =>
                    val newF = functionToFunction.get(f).map{_.to}.getOrElse(f)
                    newF.fullBody = replaceCalls(f.fullBody)
                    newF
                  case c : ClassDef =>
                    // val oldMethods = c.methods
                    // c.clearMethods()
                    // for (m <- oldMethods) {
                    //  c.registerMethod(functionToFunction.get(m).map{_.to}.getOrElse(m))
                    // }
                    c
                  case d =>
                    d
                }
              })
            case d => d
          }
        )
      })
    
    newP
    
  }

}
