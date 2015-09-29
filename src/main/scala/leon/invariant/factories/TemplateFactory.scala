package leon
package invariant.factories

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import scala.collection.mutable.{ Map => MutableMap }
import invariant._
import scala.collection.mutable.{Map => MutableMap}

import invariant.engine._
import invariant.util._
import invariant.structure._
import FunctionUtils._

object TemplateIdFactory {
  //a set of template ids
  private var ids = Set[Identifier]()

  def getTemplateIds : Set[Identifier] = ids

  def freshIdentifier(name : String = "", idType: TypeTree = RealType) : Identifier = {
    val idname = if(name.isEmpty()) "a?"
    			 else name + "?"
    val freshid = FreshIdentifier(idname, idType, true)
    ids += freshid
    freshid
  }

  def copyIdentifier(id: Identifier) : Identifier = {
    val freshid = FreshIdentifier(id.name, RealType, false)
    ids += freshid
    freshid
  }

   /**
   * Template variables have real type
   */
  def IsTemplateIdentifier(id : Identifier) : Boolean = {
    ids.contains(id)
  }

  def IsTemplateVar(v : Variable) : Boolean = {
    IsTemplateIdentifier(v.id)
  }

  def freshTemplateVar(name : String= "") : Variable = {
    Variable(freshIdentifier(name))
  }
}

trait TemplateGenerator {
  def getNextTemplate(fd : FunDef): Expr
}

/**
 * Templates are expressions with template variables.
 * The program variables that can be free in the templates are only the arguments and
 * the result variable.
 * Note: the program logic depends on the mutability here.
 */
class TemplateFactory(tempGen : Option[TemplateGenerator], prog: Program, reporter : Reporter) {

  //a mapping from function definition to the template
  private var templateMap = {
    //initialize the template map with predefined user maps
    var muMap = MutableMap[FunDef, Expr]()
    Util.functionsWOFields(prog.definedFunctions).foreach { fd =>
      val tmpl = fd.template
      if (tmpl.isDefined) {
        muMap.update(fd, tmpl.get)
      }
    }
    muMap
  }

  def setTemplate(fd:FunDef, tempExpr :Expr) = {
    templateMap += (fd -> tempExpr)
  }

  /**
   * This is the default template generator.
   *
   */
  def getDefaultTemplate(fd : FunDef): Expr = {

    //just consider all the arguments, return values that are integers
    val baseTerms = fd.params.filter((vardecl) => Util.isNumericType(vardecl.getType)).map(_.toVariable) ++
    					(if(Util.isNumericType(fd.returnType)) Seq(Util.getFunctionReturnVariable(fd))
    					 else Seq())

    val lhs = baseTerms.foldLeft(TemplateIdFactory.freshTemplateVar() : Expr)((acc, t)=> {
       Plus(Times(TemplateIdFactory.freshTemplateVar(),t),acc)
    })
    val tempExpr = LessEquals(lhs,InfiniteIntegerLiteral(0))
    tempExpr
  }


  /**
   * Constructs a template using a mapping from the formals to actuals.
   * Uses default template if a template does not exist for the function and no template generator is provided.
   * Otherwise, use the provided template generator
   */
  var refinementSet = Set[FunDef]()
  def constructTemplate(argmap: Map[Expr,Expr], fd: FunDef): Expr = {

    //initialize the template for the function
    if (!templateMap.contains(fd)) {
      if(!tempGen.isDefined) templateMap += (fd -> getDefaultTemplate(fd))
      else {
    	templateMap += (fd -> tempGen.get.getNextTemplate(fd))
    	refinementSet += fd
    	//for information
      	reporter.info("- Template generated for function "+fd.id+" : "+templateMap(fd))
      }
    }
    replace(argmap,templateMap(fd))
  }


  /**
   * Refines the templates of the functions that were assigned templates using the template generator.
   */
  def refineTemplates(): Boolean = {

    if(tempGen.isDefined) {
      var modifiedTemplate = false
      refinementSet.foreach((fd) => {
        val oldTemp = templateMap(fd)
        val newTemp = tempGen.get.getNextTemplate(fd)

        if (oldTemp != newTemp) {
          modifiedTemplate = true
          templateMap.update(fd, newTemp)
          reporter.info("- New template for function " + fd.id + " : " + newTemp)
        }
      })
      modifiedTemplate
    } else false
  }

  def getTemplate(fd : FunDef) : Option[Expr] = {
    templateMap.get(fd)
  }

  def getFunctionsWithTemplate : Seq[FunDef] = templateMap.keys.toSeq

}