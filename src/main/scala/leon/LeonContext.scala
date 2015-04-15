/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import leon.utils._

import java.io.File

/** Everything that is part of a compilation unit, except the actual program tree.
 *  Contexts are immutable, and so should all there fields (with the possible
 *  exception of the reporter). */
case class LeonContext(
  reporter: Reporter,
  interruptManager: InterruptManager,
  options: Seq[LeonOption[Any]] = Seq(),
  files: Seq[File] = Seq(),
  timers: TimerStorage = new TimerStorage
) {

  // @mk: This is not typesafe, because equality for options is implemented as name equality.
  // It will fail if an LeonOptionDef is passed that has the same name
  // with one in Main,allOptions, but is different
  def findOption[A](optDef: LeonOptionDef[A]): Option[A] = options.collectFirst {
    case LeonOption(`optDef`, value) => value.asInstanceOf[A]
  }

  def findOptionOrDefault[A](optDef: LeonOptionDef[A]): A =
    findOption(optDef).getOrElse(optDef.default)
}
