package leon
package invariant.structure

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import invariant.factories._
import invariant.util._
import Util._
import scala.language.implicitConversions

/**
 * Some utiliy methods for functions.
 * This also does caching to improve performance.
 */
object FunctionUtils {

  class FunctionInfo(fd: FunDef) {
    //flags
    lazy val isTheoryOperation = fd.annotations.contains("theoryop")
    lazy val isMonotonic = fd.annotations.contains("monotonic")
    lazy val isCommutative = fd.annotations.contains("commutative")
    lazy val isDistributive = fd.annotations.contains("distributive")

    //the template function
    lazy val tmplFunctionName = "tmpl"
    /**
     * checks if the function name is 'tmpl' and there is only one argument
     * if not, type checker would anyway throw an error if leon.invariant._ is included
     */
    def isTemplateInvocation(finv: Expr) = {
      finv match {
        case FunctionInvocation(fd, args) =>
          (fd.id.name == "tmpl" && fd.returnType == BooleanType &&
            args.size == 1 && args(0).isInstanceOf[Lambda])
        case _ =>
          false
      }
    }

    def extractTemplate(tempLambda: Lambda): Expr = {
      val Lambda(vdefs, body) = tempLambda
      val vars = vdefs.map(_.id.toVariable)
      //Note that we should use real type for template variables.
      val tempVars = vars.map(v => TemplateIdFactory.freshIdentifier(v.id.name).toVariable)
      val repmap = (vars zip tempVars).toMap[Expr, Expr]
      replace(repmap, body)
    }

    lazy val (postWoTemplate, templateExpr) = {
      if (fd.postcondition.isDefined) {
        val Lambda(_, postBody) = fd.postcondition.get
        //the 'body' could be a template or 'And(pred, template)'
        postBody match {
          case finv @ FunctionInvocation(_, args) if isTemplateInvocation(finv) =>
            //println("Template expression : "+tempExpr)
            (None, Some(finv))
          case And(args) if args.exists(isTemplateInvocation) =>
            val (tempFuns, otherPreds) = args.partition {
              case a if isTemplateInvocation(a) => true
              case _ => false
            }
            if (tempFuns.size > 1) {
              throw new IllegalStateException("Multiple template functions used in the postcondition: " + postBody)
            } else {
              val rest = if (otherPreds.size <= 1) otherPreds(0) else And(otherPreds)
              (Some(rest), Some(tempFuns(0).asInstanceOf[FunctionInvocation]))
            }
          case pb =>
            (Some(pb), None)
        }
      } else (None, None)
    }

    lazy val template = templateExpr map (finv => extractTemplate(finv.args(0).asInstanceOf[Lambda]))

    def hasTemplate: Boolean = templateExpr.isDefined
    def getPostWoTemplate = postWoTemplate match {
      case None => tru
      case Some(expr) => expr
    }
    def getTemplate = template.get
  }

  // a cache for function infos
  private var functionInfos = Map[FunDef, FunctionInfo]()
  implicit def funDefToFunctionInfo(fd: FunDef): FunctionInfo = {
    functionInfos.getOrElse(fd, {
      val info = new FunctionInfo(fd)
      functionInfos += (fd -> info)
      info
    })
  }
}