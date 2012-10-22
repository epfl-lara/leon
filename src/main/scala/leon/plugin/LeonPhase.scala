package leon
package plugin

import purescala.Definitions.Program

abstract class LeonPhase {
  val name: String
  val description: String

  def run(ac: LeonContext): LeonContext
}

abstract class TransformationPhase extends LeonPhase {
  def apply(p: Program): Program

  override def run(ac: LeonContext) = ac.copy(program = apply(ac.program))
}

abstract class UnitPhase extends LeonPhase {
  def apply(p: Program): Unit

  override def run(ac: LeonContext) = { apply(ac.program); ac }
}
