/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package codegen

import scala.util.control.NonFatal

import purescala.Common._
import purescala.Definitions._

import cafebabe._
import cafebabe.ClassFileTypes.U2
import cafebabe.Flags._

object CodeGenPhase extends LeonPhase[Program,CompilationResult] {
  val name = "CodeGen"
  val description = "Compiles a Leon program into Java methods"

  def run(ctx : LeonContext)(p : Program) : CompilationResult = {
    try {
      val unit = new CompilationUnit(ctx, p);
      unit.writeClassFiles()
      CompilationResult(successful = true)
    } catch {
      case NonFatal(e) => CompilationResult(successful = false)
    }

  } 
}
