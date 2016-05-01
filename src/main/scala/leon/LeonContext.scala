/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import leon.utils._

import java.io.File

import scala.reflect.ClassTag

/** Everything that is part of a compilation unit, except the actual program tree.
  * LeonContexts are immutable, and so should all their fields (with the possible
  * exception of the reporter).
  */
case class LeonContext(
  reporter: Reporter,
  interruptManager: InterruptManager,
  options: Seq[LeonOption[Any]] = Seq(),
  files: Seq[File] = Seq(),
  classDir: Option[File] = None,
  timers: TimerStorage = new TimerStorage
) {

  def findOption[A: ClassTag](optDef: LeonOptionDef[A]): Option[A] = options.collectFirst {
    case LeonOption(`optDef`, value:A) => value
  }

  def findOptionOrDefault[A: ClassTag](optDef: LeonOptionDef[A]): A =
    findOption(optDef).getOrElse(optDef.default)

  def toSctx = solvers.SolverContext(this, new evaluators.EvaluationBank)
}

object LeonContext {
  def empty = {
    val reporter = new DefaultReporter(Set())
    LeonContext(reporter, new InterruptManager(reporter))
  }

  def printNames = {
    val reporter = new DefaultReporter(Set())
    LeonContext(
      reporter,
      new InterruptManager(reporter),
      options = Seq(LeonOption[Set[DebugSection]](GlobalOptions.optDebug)(Set(DebugSectionTrees)))
    )
  }
}
