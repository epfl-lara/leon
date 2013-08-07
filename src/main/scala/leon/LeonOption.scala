/* Copyright 2009-2013 EPFL, Lausanne */

package leon

/** Describes a command-line option. */
sealed abstract class LeonOption {
  val name: String
}

/** Boolean (on/off) options. Present means "on". */
case class LeonFlagOption(name: String, value: Boolean) extends LeonOption {
  override def toString() : String = {
    if (value) {
      "--" + name
    } else {
      "--" + name + "=off"
    }
  }
}

/** Options of the form --option=value. */
case class LeonValueOption(name: String, value: String) extends LeonOption {
  def splitList : Seq[String] = value.split(':').map(_.trim).filter(!_.isEmpty)

  def asInt(ctx : LeonContext) : Option[Int] = try {
    Some(value.toInt)
  } catch {
    case _ : Throwable =>
      ctx.reporter.error("Option --%s takes an integer as value.".format(name))
      None
  }

  override def toString() : String = "--%s=%s".format(name, value)
}

sealed abstract class LeonOptionDef {
  val name: String
  val usageOption: String
  val usageDesc: String
}

case class LeonFlagOptionDef(name: String,
                             usageOption: String,
                             usageDesc: String,
                             default: Boolean = false) extends LeonOptionDef

case class LeonValueOptionDef(name: String,
                              usageOption: String,
                              usageDesc: String,
                              flagValue: Option[String] = None,
                              default: Option[String] = None) extends LeonOptionDef

object ListValue {
  def apply(values: Seq[String]) = values.mkString(":")
  def unapply(value: String): Option[Seq[String]] = {
    if (value == "off") {
      None
    } else {
      Some(value.split(':').map(_.trim).filter(!_.isEmpty))
    }
  }
}
