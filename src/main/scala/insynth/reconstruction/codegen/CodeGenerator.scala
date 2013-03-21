package insynth.reconstruction.codegen

import scala.text.Document
import scala.text.Document.empty

//import ch.epfl.insynth.reconstruction.intermediate._
//import ch.epfl.insynth.trees
//import ch.epfl.insynth.print._
//import ch.epfl.insynth.reconstruction.combinator.{ NormalDeclaration, AbsDeclaration }
import insynth.leon.{ LeonDeclaration => DomainDeclaration, _ }
import insynth.reconstruction.stream._

import insynth.util.format.{ FormatLeonType => FormatDomainType, FormatIntermediate }
import insynth.util.logging.HasLogger

import leon.purescala.Trees.{ Expr }
import leon.purescala.TypeTrees.{ TypeTree => DomainType, FunctionType => Function }
import leon.purescala.{ TypeTrees => domain }
import leon.purescala.Trees.{ Expr => CodeGenOutput }

/**
 * class that converts an intermediate tree into a list of output elements (elements
 * capable of Scala code generation)
 * should be extended to provide syntax-style variants
 */
class CodeGenerator extends (Node => CodeGenOutput) with HasLogger {

  /**
   * takes the tree and calls the recursive function and maps documents to Output elements
   * @param tree root of intermediate (sub)tree to transform
   * @return list of output (code snippet) elements
   */
  def apply(tree: Node) = {
    // match the starting tree to an application that produces query type
    tree match {
      case Application(domain.FunctionType(_, _ /* BottomType */), queryDec :: List(innerApp)) =>
      	transform(innerApp)
      case _ => throw new RuntimeException
    }
  }
  
  /** transform context determines the place of the element to transform */
  object TransformContext extends Enumeration {
    type TransformContext = Value
    // expression, application, parameter, argument (in a function), single parameter
    val Expr, App, Par, Arg, SinglePar = Value
  }
  // import all transform context values
  import TransformContext._
  
  /**
   * main method (recursive) for transforming a intermediate (sub)tree
   * @param tree root node of the (sub)tree to transform 
   * @return list of documents containing all combinations of available expression for
   * the given (sub)tree
   */
  def transform(tree: Node): CodeGenOutput = {    
    tree match {
      // variable (declared previously as arguments)
      case Variable(tpe, name) =>
        // what to do here
        throw new RuntimeException
      // identifier from the scope
      case Identifier(tpe, DomainDeclaration(_, _, _, im: ImmediateExpression)) => 
        im()
      // apply parameters in the tail of params according to the head of params 
      case app@Application(tpe, params) => {        
        // match the application definition term
        params.head match {
          case Identifier(_, decl)  => {            
	          info("Generating application: " + decl + " with params: " + params + " params.size = " + params.size)   

	          // for an expression of each parameters yield the appropriate transformed expression	            
            val paramsExpr: List[CodeGenOutput] = params.tail.map(transform _)
	               
            decl.expression match {
              // identifier is a function
              case NaryReconstructionExpression(_, fun) =>  
		            info("NaryReconstructionExpression with params: " + paramsExpr + " paramsExpr.size = " + paramsExpr.size)  
                assert(paramsExpr.size >= 1)             
                
                // return application of transformed parameters to fun
                fun(paramsExpr)
                
              // identifier is an immediate expression
              case ImmediateExpression(_, expr) =>
                assert(paramsExpr.isEmpty)
                expr
                
              // identifier is an unary operator
              case UnaryReconstructionExpression(_, fun) =>
                assert(paramsExpr.size == 1)
                fun(paramsExpr.head)
                
              // this should not happen
              case _ => throw new RuntimeException
            }
          } // case Identifier
          
          case innerApp@Application(appType: domain.FunctionType, params) =>
            warning("cannot have app head: " + innerApp + " in application " + app)
          	throw new RuntimeException
                      
          // function that is created as an argument or anything else
          case /*Identifier(_, _:AbsDeclaration) | */_:Variable | _ =>
          	throw new RuntimeException
          	
        } // params.head match 
      }
      
      // abstraction first creates all of its arguments
      case Abstraction(tpe, vars, subtrees) =>
        assert(vars.size > 0)        
        throw new RuntimeException
        
    } // tree match
  }
  
}