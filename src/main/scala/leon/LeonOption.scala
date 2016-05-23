/* Copyright 2009-2016 EPFL, Lausanne */

package leon

import OptionParsers._

import purescala.Definitions._
import purescala.DefOps.fullName

import scala.util.Try

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
    f"$usageDesc%-28s" + description.replaceAll("\n", "\n" + " " * 28)
  }

  private def parseValue(s: String)(implicit reporter: Reporter): A = {
    parser(s).getOrElse(
      reporter.fatalError(
        s"Invalid option usage: --$name\n" +
        "Try 'leon --help' for more information."
      )
    )
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
  val parser = booleanParser
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
  override def hashCode = optionDef.hashCode + value.hashCode
}

object LeonOption {
  def apply[A](optionDef: LeonOptionDef[A])(value: A) = {
    new LeonOption(optionDef, value)
  }
  def unapply[A](opt: LeonOption[A]) = Some((opt.optionDef, opt.value))
}

object OptionParsers {
  type OptionParser[A] = String => Option[A]

  val longParser: OptionParser[Long] = { s =>
    Try(s.toLong).toOption
  }
  val stringParser: OptionParser[String] = Some(_)
  val booleanParser: OptionParser[Boolean] = {
    case "on"  | "true"  | "yes" | "" => Some(true)
    case "off" | "false" | "no"       => Some(false)
    case _  => None
  }

  def seqParser[A](base: OptionParser[A]): OptionParser[Seq[A]] = s => {
    @inline def foo: Option[Seq[A]] = Some(
      s.split(",")
        .filter(_.nonEmpty)
        .map(base andThen (_.getOrElse(return None)))
    )
    foo
  }
  def setParser[A](base: OptionParser[A]): OptionParser[Set[A]] = {
    seqParser(base)(_).map(_.toSet)
  }

}


object OptionsHelpers {

  private val matcher = s"--(.*)=(.*)".r
  private val matcherWithout = s"--(.*)".r

  def nameValue(s: String) = s match {
    case matcher(name, value) => Some(name, value)
    case matcherWithout(name) => Some(name, "")
    case _ => None
  }

  // helper for options that include patterns

  def matcher(patterns: Traversable[String]): String => Boolean = {
    val regexPatterns = patterns map { s =>
      import java.util.regex.Pattern

      // wildcards become ".*", rest is quoted.
      var p = s.split("_").toList.map(Pattern.quote).mkString(".*")

      // We account for _ at begining and end
      if (s.endsWith("_")) {
        p += ".*"
      }

      if (s.startsWith("_")) {
        p = ".*"+p
      }

      // Finally, we match qualified suffixes (e.g. searching for 'size' will
      // match 'List.size' but not 'thesize')
      Pattern.compile("(.+\\.)?"+p)
    }

    (name: String) => regexPatterns.exists(p => p.matcher(name).matches())
  }

  def fdMatcher(pgm: Program)(patterns: Traversable[String]): FunDef => Boolean = {
    { (fd: FunDef) => fullName(fd)(pgm) } andThen matcher(patterns)
  }

  def filterInclusive[T](included: Option[T => Boolean], excluded: Option[T => Boolean]): T => Boolean = {
    included match {
      case Some(i) =>
        i
      case None =>
        excluded match {
          case Some(f) => (t: T) => !f(t)
          case None    => (t: T) => true
        }
    }
  }
}
