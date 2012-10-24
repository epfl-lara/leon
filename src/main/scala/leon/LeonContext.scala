package leon

import purescala.Definitions.Program

case class LeonContext(
  val settings: Settings          = Settings(),
  val reporter: Reporter          = new DefaultReporter
)

