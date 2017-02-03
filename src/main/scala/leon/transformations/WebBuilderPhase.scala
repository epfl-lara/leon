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
import scala.xml.MinimizeMode
import scala.xml.NamespaceBinding
import scala.xml.EntityRef
import scala.xml.ProcInstr
import scala.xml.Atom
import scala.xml.Node
import scala.xml.Group
import scala.xml.Text
import scala.xml.Comment
import scala.xml.Utility
import scala.xml.TextBuffer
import scala.xml.XML

object WebBuilderPhase extends SimpleLeonPhase[Program, String] {
  val name = "Web Builder"
  val description = "Generates a stand-alone HTML page from code having a Main.main method using webbuilder."
  val optArguments = LeonStringOptionDef("a", "Top-level val override", "", "var1:value1;var2:value2")
  override val definedOptions: Set[leon.LeonOptionDef[Any]] = Set(optArguments)
  
  def updateValsInProgram(ctx: LeonContext, pgm: Program): Unit = {
    val valOverride = ctx.findOptionOrDefault(optArguments)
    
    if(valOverride != "") {
      for{c <- valOverride.split(";")
          Array(k, v) = c.split(":")}{
        pgm.lookupFunDef("Main." + k) match {
          case None => println("Warning: Could not find a definition Main." + k + " to override. Ignored")
          case Some(fd) => 
            fd.returnType match {
              case StringType =>
                fd.body = Some(StringLiteral(v))
              case BooleanType =>
                fd.body = Some(BooleanLiteral(v=="true"))
              case Int32Type =>
                fd.body = Some(IntLiteral(Integer.parseInt(v)))
              case IntegerType =>
                fd.body = Some(InfiniteIntegerLiteral(BigInt(Integer.parseInt(v))))
            }
            
        }
      }
    }
    
  }
  
  def apply(ctx: LeonContext, pgm: Program): String = {
    println("Starting to evaluate with webBuilder...")
    updateValsInProgram(ctx, pgm)
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
<link id="revealcsslink" rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/reveal.js/css/reveal.css"></link>
<link id="themewebbuilder" rel="stylesheet" media="screen" href="http://leondev.epfl.ch/assets/reveal.js/css/theme/simple.css"></link>
<script src="http://leondev.epfl.ch/assets/client-jsdeps.min.js"></script>
<script>var WBProductionVersion = true</script>
{css}</head><body>{elems}{javascript}
<div style="position: fixed;bottom: 0;right: 0;color: #ddd;margin: 0px 20px 5px 0px;">Generated by <a style="color: #ddf" href="http://leon.epfl.ch">WebBuilder</a></div></body> </html>

    val p =new AugmentedPrettyPrinter(1200, 2)
    val formatted = "<!DOCTYPE html>\n" +
        p.format(html).replace(scriptplaceholder,
        finalCode.replaceAll("\"/assets", "\"http://leondev.epfl.ch/assets"))
    formatted
  }
  
  private class AugmentedDefaultEvaluator(ctx: LeonContext, prog: Program, bank: EvaluationBank = new EvaluationBank)
  extends RecursiveEvaluator(ctx, prog, bank, Int.MaxValue)
     with HasDefaultGlobalContext
     with HasDefaultRecContext
     
  private class AugmentedPrettyPrinter(width: Int, step: Int) extends scala.xml.PrettyPrinter(width,step) {
    val minimizeMode = MinimizeMode.Never
    def doPreserve1(node: Node) =
      node.attribute(XML.namespace, XML.space).map(_.toString == XML.preserve) getOrElse false
    override protected def traverse(node: Node, pscope: NamespaceBinding, ind: Int): Unit =  node match {
      case Text(s) if s.trim() == "" =>
        ;
      case _:Atom[_] | _:Comment | _:EntityRef | _:ProcInstr =>
        makeBox( ind, node.toString.trim() )
      case g @ Group(xs) =>
        traverse(xs.iterator, pscope, ind)
      case _ =>
        val test = {
          val sb = new StringBuilder()
          Utility.serialize(node, pscope, sb, stripComments = false, minimizeTags = minimizeMode)
          if (doPreserve1(node)) sb.toString
          else TextBuffer.fromString(sb.toString).toText(0).data
        }
        if (childrenAreLeaves(node) && fits(test)) {
          makeBox(ind, test)
        } else {
          val (stg, len2) = startTag(node, pscope)
          val etg = endTag(node)
          if (stg.length < width - cur) { // start tag fits
            makeBox(ind, stg)
            makeBreak()
            traverse(node.child.iterator, node.scope, ind + step)
            makeBox(ind, etg)
          } else if (len2 < width - cur) {
            // <start label + attrs + tag + content + end tag
            makeBox(ind, stg.substring(0, len2))
            makeBreak() // todo: break the rest in pieces
            /*{ //@todo
             val sq:Seq[String] = stg.split(" ");
             val it = sq.iterator;
             it.next;
             for (c <- it) {
               makeBox(ind+len2-2, c)
               makeBreak()
             }
             }*/
            makeBox(ind, stg.substring(len2, stg.length))
            makeBreak()
            traverse(node.child.iterator, node.scope, ind + step)
            makeBox(cur, etg)
            makeBreak()
          } else { // give up
            makeBox(ind, test)
            makeBreak()
          }
        }
    }
  }
}