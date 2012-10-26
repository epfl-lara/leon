package leon

import purescala.Definitions.Program

case class LeonContext(
  val settings: Settings          = Settings(),
  val options: List[LeonOption]   = Nil,
  val files: List[String]         = Nil,
  val reporter: Reporter          = new DefaultReporter
)

