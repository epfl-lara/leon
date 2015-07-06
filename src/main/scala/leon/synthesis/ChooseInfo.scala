/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package synthesis

import purescala.Definitions._
import purescala.Constructors._
import purescala.Expressions._
import purescala.ExprOps._
import Witnesses._

case class ChooseInfo(fd: FunDef,
                      pc: Expr,
                      source: Expr,
                      ch: Choose,
                      eb: ExampleBank) {

  val problem = Problem.fromChooseInfo(this)
}

object ChooseInfo {
  def extractFromProgram(ctx: LeonContext, prog: Program): List[ChooseInfo] = {

    // Look for choose()
    val results = for (f <- prog.definedFunctions if f.body.isDefined;
                       ci <- extractFromFunction(ctx, prog, f)) yield {
      ci
    }

    results.sortBy(_.source.getPos)
  }

  def extractFromFunction(ctx: LeonContext, prog: Program, fd: FunDef): Seq[ChooseInfo] = {

    val actualBody = and(fd.precondition.getOrElse(BooleanLiteral(true)), fd.body.get)
    val term = Terminating(fd.typed, fd.params.map(_.id.toVariable))

    val userEb = new ExamplesFinder(ctx, prog).extractExampleBank(fd)

    for ((ch, path) <- new ChooseCollectorWithPaths().traverse(actualBody)) yield {
      val eb = if (path == BooleanLiteral(true)) {
        userEb
      } else {
        ExampleBank.empty
      }

      ChooseInfo(fd, and(path, term), ch, ch, eb)
    }
  }
}
