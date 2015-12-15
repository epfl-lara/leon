package leon
package laziness

import invariant.factories._
import invariant.util.Util._
import invariant.util._
import invariant.structure.FunctionUtils._
import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Extractors._
import purescala.Types._
import leon.invariant.util.TypeUtil._
import leon.invariant.util.LetTupleSimplification._
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import leon.purescala.PrettyPrinter
import leon.LeonContext
import leon.LeonOptionDef
import leon.Main
import leon.TransformationPhase
import purescala.PrinterOptions

object LazinessUtil {

  def prettyPrintProgramToFile(p: Program, ctx: LeonContext, suffix: String) {
    val optOutputDirectory = new LeonOptionDef[String] {
      val name = "o"
      val description = "Output directory"
      val default = "leon.out"
      val usageRhs = "dir"
      val parser = (x: String) => x
    }
    val outputFolder = ctx.findOptionOrDefault(optOutputDirectory)
    try {
      new File(outputFolder).mkdir()
    } catch {
      case _: java.io.IOException =>
        ctx.reporter.fatalError("Could not create directory " + outputFolder)
    }

    for (u <- p.units if u.isMainUnit) {
      val outputFile = s"$outputFolder${File.separator}${u.id.toString}$suffix.scala"
      try {
        val out = new BufferedWriter(new FileWriter(outputFile))
        // remove '@' from the end of the identifier names
        val pat = new Regex("""(\w+)(@)(\w*)(\*?)(\S*)""", "base", "at", "mid", "star", "rest")
        val pgmText = pat.replaceAllIn(ScalaPrinter.apply(p),
          m => m.group("base") + m.group("mid") + (
            if (!m.group("star").isEmpty()) "S" else "") + m.group("rest"))
        //val pgmText = ScalaPrinter.apply(p)
        out.write(pgmText)
        out.close()
      } catch {
        case _: java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
      }
    }
    ctx.reporter.info("Output written on " + outputFolder)
  }

  def isLazyInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.apply"
    case _ =>
      false
  }

  def isEagerInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.eager"
    case _ =>
      false
  }

  def isInStateCall(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq()) =>
      fullName(fd)(p) == "leon.lazyeval.$.inState"
    case _ =>
      false
  }

  def isOutStateCall(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq()) =>
      fullName(fd)(p) == "leon.lazyeval.$.outState"
    case _ =>
      false
  }

  def isEvaluatedInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.isEvaluated"
    case _ => false
  }

  def isSuspInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_, _)) =>
      fullName(fd)(p) == "leon.lazyeval.$.isSuspension"
    case _ => false
  }

  def isWithStateCons(e: Expr)(implicit p: Program): Boolean = e match {
    case CaseClass(cct, Seq(_)) =>
      fullName(cct.classDef)(p) == "leon.lazyeval.$.WithState"
    case _ => false
  }

  /**
   * There are many overloads of withState functions with different number
   * of arguments. All of them should pass this check.
   */
  def isWithStateFun(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), _) =>
      fullName(fd)(p) == "leon.lazyeval.WithState.withState"
    case _ => false
  }

  def isValueInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.value"
    case _ => false
  }

  def isStarInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.$.*"
    case _ => false
  }

  def isLazyType(tpe: TypeTree): Boolean = tpe match {
    case CaseClassType(CaseClassDef(cid, _, None, false), Seq(_)) =>
      cid.name == "$"
    case _ => false
  }

  /**
   * TODO: Check that lazy types are not nested
   */
  def unwrapLazyType(tpe: TypeTree) = tpe match {
    case ctype @ CaseClassType(_, Seq(innerType)) if isLazyType(ctype) =>
      Some(innerType)
    case _ => None
  }

  def rootType(t: TypeTree): Option[AbstractClassType] = t match {
    case absT: AbstractClassType => Some(absT)
    case ct: ClassType           => ct.parent
    case _                       => None
  }

  def opNameToCCName(name: String) = {
    name.capitalize + "@"
  }

  /**
   * Convert the first character to lower case
   * and remove the last character.
   */
  def ccNameToOpName(name: String) = {
    name.substring(0, 1).toLowerCase() +
      name.substring(1, name.length() - 1)
  }

  def typeNameToADTName(name: String) = {
    "Lazy" + name
  }

  def adtNameToTypeName(name: String) = {
    name.substring(4)
  }

  def typeToFieldName(name: String) = {
    name.toLowerCase()
  }

  def closureConsName(typeName: String) = {
    "new@" + typeName
  }

  def isClosureCons(fd: FunDef) = {
    fd.id.name.startsWith("new@")
  }

  def evalFunctionName(absTypeName: String) = {
    "eval@" + absTypeName
  }

  def isEvalFunction(fd: FunDef) = {
    fd.id.name.startsWith("eval@")
  }

  def freshenTypeArguments(tpe: TypeTree): TypeTree = {
    tpe match {
      case NAryType(targs, tcons) =>
        val ntargs = targs.map {
          case targ: TypeParameter => targ.freshen
          case targ                => targ
        }
        tcons(ntargs)
    }
  }
}
