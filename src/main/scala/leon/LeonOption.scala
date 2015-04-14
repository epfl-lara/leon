/* Copyright 2009-2015 EPFL, Lausanne */

package leon

/** Describes a command-line option. */
sealed abstract class LeonOption {
  val name: String
}

/** Boolean (on/off) options. Present means "on". */
case class LeonFlagOption(name: String, value: Boolean) extends LeonOption {
  override def toString: String = {
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
      ctx.reporter.error(s"Option --$name takes an integer as value.")
      None
  }

  def asLong(ctx : LeonContext) : Option[Long] = try {
    Some(value.toLong)
  } catch {
    case _ : Throwable =>
      ctx.reporter.error(s"Option --$name takes a long as value.")
      None
  }

  override def toString: String = s"--$name=$value"
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
      Some(value.split("[:,]").map(_.trim).filter(!_.isEmpty))
    }
  }
}

object OptionsHelpers {
  // helper for options that include patterns

  def matcher(patterns: Traversable[String]): String => Boolean = {
    val regexPatterns = patterns map { s =>
      import java.util.regex.Pattern

      val p0 = scala.reflect.NameTransformer.encode(s)
      val p = p0.replaceAll("\\$","\\\\\\$").replaceAll("\\.", "\\\\.").replaceAll("_", ".+") 
      Pattern.compile(p)
    }

    { (name: String) => regexPatterns.exists(p => p.matcher(name).matches()) }
  }

  import purescala.Definitions.FunDef

  def fdMatcher(patterns: Traversable[String]): FunDef => Boolean = {
    { (fd: FunDef) => fd.id.name } andThen matcher(patterns)
  }

  def filterInclusive[T](included: Option[T => Boolean], excluded: Option[T => Boolean]): T => Boolean = {
    included match {
      case Some(i) =>
        i
      case None =>
        excluded match {
          case Some(f) =>
            { (t: T) => !f(t) }

          case None =>
            { (t: T) => true }
        }
    }
  }
}
