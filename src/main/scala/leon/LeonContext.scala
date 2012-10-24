package leon

import purescala.Definitions.Program

case class LeonContext(
  val options: List[String] = List(),
  val program: Option[Program] = None,
  val reporter: Reporter = new DefaultReporter
)

