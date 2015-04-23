/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import OptionParsers._

abstract class LeonOptionDef[+A] {
  val name: String
  val description: String
  val default: A
  val parser: OptionParser[A]
  val usageRhs: String
  def usageDesc = {
    if (usageRhs.isEmpty) s"--$name"
    else s"--$name=$usageRhs"
  }
  def helpString = {
    f"$usageDesc%-22s" + description.replaceAll("\n", "\n" + " " * 22)
  }

  private def parseValue(s: String)(implicit reporter: Reporter): A = {
    try { parser(s) }
    catch {
      case _ : IllegalArgumentException =>
        reporter.error(s"Invalid option usage: $usageDesc")
        Main.displayHelp(reporter, error = true)
    }
  }

  def parse(s: String)(implicit reporter: Reporter): LeonOption[A] =
    LeonOption(this)(parseValue(s))

  def withDefaultValue: LeonOption[A] =
    LeonOption(this)(default)

  // @mk: FIXME: Is this cool?
  override def equals(other: Any) = other match {
    case that: LeonOptionDef[_] => this.name == that.name
    case _ => false
  }
  override def hashCode = name.hashCode
}

case class LeonFlagOptionDef(name: String, description: String, default: Boolean) extends LeonOptionDef[Boolean] {
  val parser = booleanParser(default)
  val usageRhs = ""
}


case class LeonStringOptionDef(name: String, description: String, default: String, usageRhs: String) extends LeonOptionDef[String] {
  val parser = stringParser
}

case class LeonLongOptionDef(name: String, description: String, default: Long, usageRhs: String) extends LeonOptionDef[Long] {
  val parser = longParser
}


class LeonOption[+A] private (val optionDef: LeonOptionDef[A], val value: A) {
  override def toString = s"--${optionDef.name}=$value"
  override def equals(other: Any) = other match {
    case LeonOption(optionDef, value) =>
      optionDef.name == this.optionDef.name && value == this.value
    case _ => false
  }
  override def hashCode = optionDef.hashCode
}

object LeonOption {
  def apply[A](optionDef: LeonOptionDef[A])(value: A) = {
    new LeonOption(optionDef, value)
  }
  def unapply[A](opt: LeonOption[A]) = Some((opt.optionDef, opt.value))
}

object OptionParsers {
  type OptionParser[A] = String => A

  val longParser: OptionParser[Long] = _.toLong
  val stringParser: OptionParser[String] = x => x
  def booleanParser(default: Boolean): OptionParser[Boolean] = {
    case "on"  | "true"  | "yes" | "" => true
    case "off" | "false" | "no"       => false
    case _  => throw new IllegalArgumentException
  }
  def seqParser[A](base: OptionParser[A]): OptionParser[Seq[A]] = s => {
    s.split(",").filter(_.nonEmpty).map(base)
  }
  def setParser[A](base: OptionParser[A]): OptionParser[Set[A]] = s => {
    s.split(",").filter(_.nonEmpty).map(base).toSet
  }

}


object OptionsHelpers {

  private val matcher = s"--(.*)=(.*)".r
  private val matcherWithout = s"--(.*)".r

  def nameValue(s: String) = s match {
    case matcher(name, value) => (name, value)
    case matcherWithout(name) => (name, "")
    case _ => sys.error("") // FIXME
  }

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
