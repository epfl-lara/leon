package leon

sealed abstract class LeonOption {
  val name: String
}

case class LeonFlagOption(name: String) extends LeonOption
case class LeonValueOption(name: String, value: String) extends LeonOption {

  def splitList : Seq[String] = value.split(':').map(_.trim).filter(!_.isEmpty)
}

sealed abstract class LeonOptionDef {
  val name: String
  val usageOption: String
  val usageDesc: String
  val isFlag: Boolean
}
case class LeonFlagOptionDef(name: String, usageOption: String, usageDesc: String) extends LeonOptionDef {
  val isFlag = true
}

case class LeonValueOptionDef(name: String, usageOption: String, usageDesc: String) extends LeonOptionDef {
  val isFlag = false
}

object ListValue {
  def unapply(value: String): Option[Seq[String]] = Some(value.split(':').map(_.trim).filter(!_.isEmpty))
}
