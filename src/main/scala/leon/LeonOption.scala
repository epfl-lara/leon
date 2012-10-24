package leon

sealed abstract class LeonOption {
  val name: String
}

case class LeonFlagOption(name: String) extends LeonOption
case class LeonValueOption(name: String, value: String) extends LeonOption {

  def splitList : Seq[String] = value.split(':').map(_.trim).filter(!_.isEmpty)
}

case class LeonOptionDef(name: String, isFlag: Boolean, description: String)
