package leon
package transformations

import java.io.File
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import purescala.ScalaPrinter
import utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import invariant.util.ExpressionTransformer._
import invariant.structure.FunctionUtils._
import invariant.util.LetTupleSimplification._
import evaluators.HasDefaultRecContext
import evaluators.HasDefaultGlobalContext
import evaluators.AbstractOnlyEvaluator
import evaluators.EvaluationResults
import evaluators.RecursiveEvaluator
import evaluators.EvaluationBank
import org.apache.commons.lang3.StringEscapeUtils

object WebBuilderPhase extends UnitPhase[Program] {
  val name = "Web Builder"
  val description = "Generates a stand-alone HTML page from code having a Main.main method using webbuilder."
  val optOutputFile = LeonStringOptionDef("o", "Output file", "output.html", "file.html")
  override val definedOptions: Set[leon.LeonOptionDef[Any]] = Set(optOutputFile)
  
  def apply(ctx: LeonContext, pgm: Program): Unit = {
    println("Starting to evaluate with webBuilder...")
    val outputfilename = ctx.findOptionOrDefault(optOutputFile)
    
    val defaultEvaluator = new AugmentedDefaultEvaluator(ctx, pgm)
    
    def eval(functionName: String, allow_failures: Boolean = false): Expr = {
      val fd = pgm.lookupFunDef(functionName) match {
        case Some(funDef) => funDef
        case None => {
          if(allow_failures) return NoTree(UnitType)
          ctx.reporter.fatalError("Could not find function "+functionName)
        }
      }
      defaultEvaluator.eval(FunctionInvocation(fd.typed, List())) match {
        case EvaluationResults.Successful(res) => res
        case EvaluationResults.EvaluatorError(msg) =>
          ctx.reporter.fatalError("Evaluation of $functionName failed: evaluator returned an EvaluationError with message: "+msg)
        case EvaluationResults.RuntimeError(msg) =>
          ctx.reporter.fatalError("Evaluation of $functionName failed: evaluator returned a RuntimeError with message: "+msg)
      }
    }
    val ConsCCD = pgm.library.Cons.get
    val NilCCD = pgm.library.Nil.get
        
    object CaseClassNamed {
      def unapply(e: Expr) = e match {
        case CaseClass(CaseClassType(ccd, _), args) => Some(ccd.id.name, args.toList)
        case _ => None
      }
    }
    object CaseClassBeing {
      def unapply(e: Expr) = e match {
        case CaseClass(CaseClassType(ccd, _), args) => Some(ccd, args.toList)
        case _ => None
      }
    }
    object ListExpr {
      def unapply(leonListExpr: Expr): Option[List[Expr]] = leonListExpr match {
        case CaseClassBeing(ConsCCD, List(elem, ListExpr(res))) => Some(elem :: res)
        case CaseClassBeing(NilCCD, args) => Some(Nil)
        case CaseClassBeing(cd, args) => ctx.reporter.fatalError("Expected Cons or Nil, got" + cd)
        case e => ctx.reporter.fatalError("Expected Cons or Nil case class, got" + e)
      }
    }
    def convertCss(css: Expr) = css match {
      case CaseClassNamed("StyleSheet", List(
          ListExpr(styleRules))) =>
        styleRules.map{
            case CaseClassNamed("StyleRule", List(
                StringLiteral(target), ListExpr(webStyles))
                ) =>
                 target + " {\n" + webStyles.map{
                   case CaseClassNamed("WebStyle", List(StringLiteral(attributeName), StringLiteral(attributeValue))) =>
                     s"  $attributeName:$attributeValue;"
                   case e => ctx.reporter.fatalError("Expected WebStyle, got" + e)
                 }.mkString("\n") + "}"
            case e => ctx.reporter.fatalError("Expected StyleRule, got" + e)
        }.mkString("\n\n")
      case CaseClassNamed(s, List(
          ListExpr(styleRules))) =>
            ctx.reporter.fatalError("Expected StyleSheet, got" + s)
      case CaseClassNamed("StyleSheet", List(
          e)) =>
            ctx.reporter.fatalError("Expected list of arguments, got" + e)
      case e => ctx.reporter.fatalError("Expected StyleSheet, got" + e)
    }
    
    def convertElement(elements: Expr): String = elements match {
      case CaseClassNamed("TextElement", List(StringLiteral(text))) =>
        xml.Utility.escape(text)
      case CaseClassNamed("Element", List(StringLiteral(tag), ListExpr(sons), ListExpr(properties), ListExpr(style))) =>
        val styles = style.map{
         case CaseClassNamed("WebStyle", List(StringLiteral(attributeName), StringLiteral(attributeValue))) =>
           s"$attributeName:$attributeValue"
         case e => ctx.reporter.fatalError("Expected WebStyle, got" + e)
        }.mkString(";")
        val attributes = (properties.map{
          case CaseClassNamed("WebAttribute", List(StringLiteral(name), StringLiteral(value))) =>
            name + "=\"" + StringEscapeUtils.escapeJava(value)+"\""
          case e => ctx.reporter.fatalError("Expected WebAttribute, got" + e)
        } ++ (if(styles.isEmpty) Nil else List("style=\""+StringEscapeUtils.escapeJava(styles)+"\""))).mkString(" ")
        val children = sons.map(convertElement).mkString("")
        s"<$tag $attributes>$children</$tag>"
    }
    val (elems, css) = eval("Main.main")  match {
      case CaseClassNamed("WebPage", List(elements, css)) =>
        val cssstring: String = convertCss(css)
        val elem = xml.XML.loadString(convertElement(elements))
        (elem, <style>{cssstring}</style>)
      case e => 
        ctx.reporter.fatalError("Evaluation failed: expected WebPage, got "+ e)
    }
    val scriptplaceholder = "65784191332499874133121118ScriptPlaceHolder"
    val (javascript, finalCode) = eval("Main.javascript", allow_failures=true) match {
      case StringLiteral(s) => (List(<script>{scriptplaceholder}</script>), s)
      case NoTree(UnitType) => (List(), "")
      case e => ctx.reporter.fatalError("Evaluation failed: expected string, got "+e)
    }
    val html = 
<html><head>
<link rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/lib/font-awesome/css/font-awesome.min.css"></link>
<link rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/lib/bootstrap/css/bootstrap.min.css"></link>
<link rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/lib/octicons/octicons/octicons.css"></link>
<link rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/lib/prettify/prettify.css"></link>
<link rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/leon.css"></link>
<link id="revealcsslink" rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/css/reveal.css"></link>
<link id="themewebbuilder" rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/css/theme/simple.css"></link>
<script src="http://leondev.epfl.ch/assets/client-jsdeps.min.js"></script>
{css}</head><body>{elems}{javascript}</body> </html>

    val p =new scala.xml.PrettyPrinter(1200, 4)
    val formatted = "<!DOCTYPE html>\n" +
        p.format(html).replace(scriptplaceholder,
        finalCode.replaceAll("\"/assets", "\"http://leondev.epfl.ch/assets"))
    val outputFile = new File(outputfilename)
    try {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(outputFile)
      val out = new BufferedWriter(fstream)
      out.write(formatted)
      out.close()
    }
    catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
    }
  }
  
  private class AugmentedDefaultEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends RecursiveEvaluator(ctx, prog, bank, Int.MaxValue)
     with HasDefaultGlobalContext
     with HasDefaultRecContext
}