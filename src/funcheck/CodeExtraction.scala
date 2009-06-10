package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

trait CodeExtraction {
  self: AnalysisComponent =>

  import global._
  import StructuralExtractors._
  import ExpressionExtractors._

  def findContracts(tree: Tree): Unit = tree match {
    case DefDef(/*mods*/ _, name, /*tparams*/ _, /*vparamss*/ _, /*tpt*/ _, body) => {
      var realBody = body
      var reqCont: Option[Tree] = None
      var ensCont: Option[Function] = None

      body match {
        case EnsuredExpression(body2, contract) => realBody = body2; ensCont = Some(contract)
        case _ => ;
      }

      realBody match {
        case RequiredExpression(body3, contract) => realBody = body3; reqCont = Some(contract)
        case _ => ;
      }

      println("In: " + name) 
      println("  Requires clause: " + reqCont)
      println("  Ensures  clause: " + ensCont)
      println("  Body:            " + realBody)
    }

    case _ => ;
  }

  def extractCode(unit: CompilationUnit): Unit = { 
    def trav(tree: Tree): Unit = tree match {
      case d @ DefDef(mods, name, tparams, vparamss, tpt, body) if !d.symbol.isConstructor => {
        println("In: " + name)
        println(d.symbol)
        println(d.mods)
          
        toPureScala(unit)(body) match {
          case Some(t) => println("  the body was extracted as: " + t)
          case None => println("  the body could not be extracted. Is it pure Scala?")
        }
      }
      case _ => ;
    }

    (new ForeachTreeTraverser(trav)).traverse(unit.body)

  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class ImpureCodeEncounteredException(tree: Tree) extends Exception

  /** Attempts to convert a scalac AST to a pure scala AST. */
  def toPureScala(unit: CompilationUnit)(tree: Tree): Option[Expr] = {
    try {
      Some(scala2PureScala(unit, false)(tree))
    } catch {
      case ImpureCodeEncounteredException(_) => None
    }
  }

  /** Forces conversion from scalac AST to purescala AST, throws an Exception
   * if impossible. If not in 'silent mode', non-pure AST nodes are reported as
   * errors. */
  private def scala2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Tree): Expr = {
    tree match {
      case ExInt32Literal(v) => IntLiteral(v)
      case ExBooleanLiteral(v) => BooleanLiteral(v)

      // default behaviour is to complain :)
      case _ => {
        if(!silent) {
          unit.error(tree.pos, "Could not extract as PureScala.")
        }
        throw ImpureCodeEncounteredException(tree)
      }
    }
  }
}
