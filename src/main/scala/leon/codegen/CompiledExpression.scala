/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import runtime.{LeonCodeGenRuntimeMonitor => LM }

import java.lang.reflect.InvocationTargetException

class CompiledExpression(unit: CompilationUnit, cf: ClassFile, expression : Expr, argsDecl: Seq[Identifier]) {

  private lazy val cl = unit.loader.loadClass(cf.className)
  private lazy val meth = cl.getMethods()(0)

  private val exprType = expression.getType

  private val params = unit.params

  def argsToJVM(args: Seq[Expr], monitor: LM): Seq[AnyRef] = {
    args.map(unit.exprToJVM(_)(monitor))
  }

  def evalToJVM(args: Seq[AnyRef], monitor: LM): AnyRef = {
    assert(args.size == argsDecl.size)

    val realArgs = if (params.requireMonitor) {
      monitor +: args
    } else {
      args
    }

    if (realArgs.isEmpty) {
      meth.invoke(null)
    } else {
      meth.invoke(null, realArgs.toArray : _*)
    }
  }

  // This may throw an exception. We unwrap it if needed.
  // We also need to reattach a type in some cases (sets, maps).
  def evalFromJVM(args: Seq[AnyRef], monitor: LM) : Expr = {
    try {
      val result = unit.jvmToExpr(evalToJVM(args, monitor))
      if(!result.isTyped) {
        result.setType(exprType)
      }
      result
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }

  def eval(args: Seq[Expr]) : Expr = {
    try {
      val monitor = 
        new LM(params.maxFunctionInvocations)
      evalFromJVM(argsToJVM(args, monitor),monitor)
    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }
  
  

  // Apply function recursively howMany times, which is of type (A, Int) => A
  // Memoization-specific
  // FIXME: Could write straight bytecode for this
  def recEval(arg: Expr, howMany : Int) : Expr = {
    try {
      // pseudorandom input
      def psr(i : Int) = (347837 * i + 983876) % 98291
     
      val monitor = new codegen.runtime.LeonCodeGenRuntimeMonitor(unit.params.maxFunctionInvocations)
      var jvmArg = unit.exprToJVM(arg)(monitor)
      var i = howMany
      while(i > 0) { 
        val jvmInp = unit.exprToJVM(IntLiteral(psr(i)))(monitor)
        jvmArg = evalToJVM(Seq(jvmArg,jvmInp),monitor)
        i = i - 1
      }

      unit.jvmToExpr(jvmArg)

    } catch {
      case ite : InvocationTargetException => throw ite.getCause()
    }
  }


} 
