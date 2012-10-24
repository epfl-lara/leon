package leon
package plugin

import purescala.Definitions.Program

case class LeonContext(
  val program: Program,
  val reporter: Reporter
)

