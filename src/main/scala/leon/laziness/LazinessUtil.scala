package leon
package laziness

import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.DefOps._
import purescala.Types._
import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter
import scala.util.matching.Regex
import utils.FileOutputPhase

object LazinessUtil {

  def isMemoized(fd: FunDef) = {
    fd.flags.contains(Annotation("memoize", Seq()))
  }

  def prettyPrintProgramToFile(p: Program, ctx: LeonContext, suffix: String, uniqueIds: Boolean = false) {
    val optOutputDirectory = FileOutputPhase.optOutputDirectory
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
        val plainText = ScalaPrinter.apply(u, purescala.PrinterOptions(printUniqueIds = uniqueIds))
        //println("Plain text: "+plainText)
        // remove '@' from the end of the identifier names
        val pat = new Regex("""(\w+)(@)(\w*)(\*?)(\S*)""", "base", "at", "mid", "star", "rest")

        val pgmText = try{ pat.replaceAllIn(plainText,
          m => {
            m.group("base") + m.group("mid") + (
              if (!m.group("star").isEmpty()) "S" else "") + m.group("rest")
          })
        } catch {
          case _: IndexOutOfBoundsException => plainText
        }
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
      fullName(fd)(p) == "leon.lazyeval.$"
    case _ =>
      false
  }

  def isEagerInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.eager"
    case _ =>
      false
  }

  def isInStateCall(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq()) =>
      val fn = fullName(fd)(p)
      (fn == "leon.lazyeval.inState" || fn == "leon.mem.inState")
    case _ =>
      false
  }

  def isOutStateCall(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq()) =>
      val fn = fullName(fd)(p)
      (fn == "leon.lazyeval.outState" || fn == "leon.mem.outState")
    case _ =>
      false
  }

  def isEvaluatedInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.Lazy.isEvaluated"
    case _ => false
  }

  def isSuspInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_, _)) =>
      fullName(fd)(p) == "leon.lazyeval.Lazy.isSuspension"
    case _ => false
  }

  def isWithStateCons(e: Expr)(implicit p: Program): Boolean = e match {
    case CaseClass(cct, Seq(_)) =>
      val fn = fullName(cct.classDef)(p)
      (fn == "leon.lazyeval.WithState" || fn == "leon.mem.memWithState")
    case _ => false
  }

  def isMemCons(e: Expr)(implicit p: Program): Boolean = e match {
    case CaseClass(cct, Seq(_)) =>
      fullName(cct.classDef)(p) == "leon.mem.Mem"
    case _ => false
  }

  /**
   * There are many overloads of withState functions with different number
   * of arguments. All of them should pass this check.
   */
  def isWithStateFun(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), _) =>
      val fn = fullName(fd)(p)
      (fn == "leon.lazyeval.WithState.withState" ||
          fn == "leon.mem.memWithState.withState")
    case _ => false
  }

  def isCachedInv(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.mem.Mem.isCached"
    case _ => false
  }

  def isValueInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.Lazy.value"
    case _ => false
  }

  def isStarInvocation(e: Expr)(implicit p: Program): Boolean = e match {
    case FunctionInvocation(TypedFunDef(fd, _), Seq(_)) =>
      fullName(fd)(p) == "leon.lazyeval.Lazy.*"
    case _ => false
  }

  def isLazyType(tpe: TypeTree): Boolean = tpe match {
    case CaseClassType(ccd, Seq(_)) if !ccd.hasParent && !ccd.isCaseObject =>
      ccd.id.name == "Lazy"
    case _ => false
  }

  def isMemType(tpe: TypeTree): Boolean = tpe match {
    case CaseClassType(ccd, Seq(_)) if !ccd.hasParent && !ccd.isCaseObject =>
      ccd.id.name == "Mem"
    case _ => false
  }

  /**
   * Lazy types are not nested by precondition
   */
  def unwrapLazyType(tpe: TypeTree) = tpe match {
    case ctype @ CaseClassType(_, Seq(innerType)) if isLazyType(ctype) || isMemType(ctype) =>
      Some(innerType)
    case _ => None
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

  def isStateParam(id: Identifier) = {
    id.name.startsWith("st@")
  }

  def isPlaceHolderTParam(tp: TypeParameter) = {
    tp.id.name.endsWith("@")
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
