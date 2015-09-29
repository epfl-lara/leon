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
    lazy val compose = fd.annotations.contains("compose")

    //the template function
    lazy val tmplFunctionName = "tmpl"
    /**
     * checks if the function name is 'tmpl' and there is only one argument
     * if not, type checker would anyway throw an error if leon.invariant._ is included
     */
    def isTemplateInvocation(finv: Expr) = {
      finv match {
        case FunctionInvocation(funInv, args) =>
          (funInv.id.name == "tmpl" && funInv.returnType == BooleanType &&
            args.size == 1 && args(0).isInstanceOf[Lambda])
        case _ =>
          false
      }
    }

    def isQMark(e: Expr) = e match {
      case FunctionInvocation(TypedFunDef(fd, Seq()), args) =>
        (fd.id.name == "?" && fd.returnType == IntegerType &&
          args.size <= 1)
      case _ => false
    }

    def extractTemplateFromLambda(tempLambda: Lambda): Expr = {
      val Lambda(vdefs, body) = tempLambda
      val vars = vdefs.map(_.id.toVariable)
      val tempVars = vars.map { // reuse template variables if possible
        case v if TemplateIdFactory.IsTemplateIdentifier(v.id) => v
        case v =>
          TemplateIdFactory.freshIdentifier(v.id.name).toVariable
      }
      val repmap = (vars zip tempVars).toMap[Expr, Expr]
      replace(repmap, body)
    }

    def tmplFunction(paramTypes: Seq[TypeTree]) = {
      val lambdaType = FunctionType(paramTypes, BooleanType)
      val paramid = FreshIdentifier("lamb", lambdaType)
      new FunDef(FreshIdentifier("tmpl", BooleanType), Seq(), BooleanType, Seq(ValDef(paramid)))
    }

    /**
     * Repackages '?' mark expression into tmpl functions
     */
    def qmarksToTmplFunction(ine: Expr) = {
      var tempIds = Seq[Identifier]()
      var indexToId = Map[BigInt, Identifier]()
      val lambBody = simplePostTransform {
        case q @ FunctionInvocation(_, Seq()) if isQMark(q) => // question mark with zero args
          val freshid = TemplateIdFactory.freshIdentifier("q")
          tempIds :+= freshid
          freshid.toVariable

        case q @ FunctionInvocation(_, Seq(InfiniteIntegerLiteral(index))) if isQMark(q) => //question mark with one arg
          indexToId.getOrElse(index, {
            val freshid = TemplateIdFactory.freshIdentifier("q" + index)
            tempIds :+= freshid
            indexToId += (index -> freshid)
            freshid
          }).toVariable

        case other => other
      }(ine)
      FunctionInvocation(TypedFunDef(tmplFunction(tempIds.map(_.getType)), Seq()),
        Seq(Lambda(tempIds.map(id => ValDef(id)), lambBody)))
    }

    /**
     * Does not support mixing of tmpl exprs and '?'.
     * Need to check that tmpl functions are not nested.
     */
    lazy val (postWoTemplate, templateExpr) = {
      if (fd.postcondition.isDefined) {
        val Lambda(_, postBody) = fd.postcondition.get
        // collect all terms with question marks and convert them to a template
        val postWoQmarks = postBody match {
          case And(args) if args.exists(exists(isQMark) _) =>
            val (tempExprs, otherPreds) = args.partition {
              case a if exists(isQMark)(a) => true
              case _ => false
            }
            //println(s"Otherpreds: $otherPreds ${qmarksToTmplFunction(Util.createAnd(tempExprs))}")
            Util.createAnd(otherPreds :+ qmarksToTmplFunction(Util.createAnd(tempExprs)))
          case pb if exists(isQMark)(pb) =>
            qmarksToTmplFunction(pb)
          case other => other
        }
        //the 'body' could be a template or 'And(pred, template)'
        postWoQmarks match {
          case finv @ FunctionInvocation(_, args) if isTemplateInvocation(finv) =>
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
      } else {
        (None, None)
      }
    }

    lazy val template = templateExpr map (finv => extractTemplateFromLambda(finv.args(0).asInstanceOf[Lambda]))

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