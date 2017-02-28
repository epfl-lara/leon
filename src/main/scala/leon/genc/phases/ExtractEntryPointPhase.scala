/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import purescala.Definitions.{ Definition, FunDef, Program }
import purescala.Types.{ Int32Type, UnitType }

/*
 * Find the main & _main functions and perform a few sanity checks.
 *
 * This phase checks that:
 *  - there is only one main unit;
 *  - the main function is uniquely defined as a non-generic external function;
 *  - the _main function is uniquely defined as a non-generic, parameterless function;
 *  - _main return type is either Unit or Int.
 */
private[genc] object ExtractEntryPointPhase extends TimedLeonPhase[Program, Definition] {
  val name = "Compute main function dependencies"
  val description = "Check validity of main & _main functions, and identify their dependencies"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("extract main")

  def apply(ctx: LeonContext, prog: Program) = getEntryPoint(prog, MiniReporter(ctx))

  // Find _main() and check the assumptions listed above
  private def getEntryPoint(prog: Program, reporter: MiniReporter): FunDef = {
    import reporter._
    import ExtraOps._

    val mainUnit = {
      val mainUnits = prog.units filter { _.isMainUnit }

      // Make sure exactly one main unit is defined -- this is just a sanity check
      if (mainUnits.size == 0) fatalError("No main unit in the program")
      if (mainUnits.size >= 2) fatalError("Multiple main units in the program")

      mainUnits.head
    }

    def getFunDef(name: String): FunDef = {
      val results = mainUnit.definedFunctions filter { _.id.name == name }

      // Make sure there is no ambiguity about the name and that the function is defined
      if (results.size == 0) fatalError(s"No $name was defined in unit ${mainUnit.id.uniqueName}")
      if (results.size == 2) fatalError(s"Multiple $name were defined in unit ${mainUnit.id}")

      results.head
    }

    val mainFd = getFunDef("main")
    val _mainFd = getFunDef("_main")

    // Checks that "main" is properly defined
    if (mainFd.isGeneric)
      fatalError("The main function should not be generic", mainFd.getPos)

    if (!mainFd.isExtern)
      fatalError("It is expected for `main(args)` to be extern", mainFd.getPos)

    // Idem for "_main"
    if (_mainFd.params.size > 0)
      fatalError("_main() should have no parameter", _mainFd.getPos)

    if (_mainFd.isGeneric)
      fatalError("_main() should not be generic", _mainFd.getPos)

    if (_mainFd.isExtern)
      fatalError("_main() should not be extern", _mainFd.getPos)

    _mainFd.returnType match {
      case UnitType | Int32Type => // valid
      case _ => fatalError("_main() should either return an integer or nothing", _mainFd.getPos)
    }

    _mainFd
  }
}


