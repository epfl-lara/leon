package leon

import purescala.Definitions.Program
import java.io.File

case class LeonContext(
  val settings: Settings          = Settings(),
  val options: List[LeonOption]   = Nil,
  val files: List[File]           = Nil,
  val reporter: Reporter          = new DefaultReporter
)

