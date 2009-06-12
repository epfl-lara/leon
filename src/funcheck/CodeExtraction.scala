package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._

trait CodeExtraction extends Extractors {
  self: AnalysisComponent =>

  import global._
  import StructuralExtractors._
  import ExpressionExtractors._

  def extractCode(unit: CompilationUnit): Program = { 
    def s2ps(tree: Tree): Expr = toPureScala(unit)(tree) match {
      case Some(ex) => ex
      case None => stopIfErrors; throw new Error("unreachable")
    }

//    def trav(tree: Tree): Unit = tree match {
//      case t : Tree if t.symbol != null && t.symbol.hasFlag(symtab.Flags.SYNTHETIC) => {
//        println("Synth! " + t)
//      }
//      case d @ DefDef(mods, name, tparams, vparamss, tpt, body) if !(d.symbol.hasFlag(symtab.Flags.SYNTHETIC) || d.symbol.isConstructor) => {
//        println("In: " + name)
//        println(d.symbol)
//        println(d.mods)
//          
//        toPureScala(unit)(body) match {
//          case Some(t) => println("  the body was extracted as: " + t)
//          case None => println("  the body could not be extracted. Is it pure Scala?")
//        }
//      }
//      case _ => ;
//    }

    def extractObject(name: Identifier, tmpl: Template): ObjectDef = {
      var funDefs: List[FunDef] = Nil
      var valDefs: List[ValDef] = Nil
      var asserts: List[Expr] = Nil

      val tTrees: List[Tree] = tmpl.body

      println(tTrees)

      tTrees.foreach(tree => tree match {
        case cd @ ClassDef(_, name, tparams, impl) => {
          println("--- " + name.toString)
          println(cd.symbol.info)
          println(cd.symbol.info.parents)
        }
        case _ => ;
      })

      ObjectDef(name, Nil, Nil)
    }

    // Extraction of the definitions.
    val program = unit.body match {
      case p @ PackageDef(name, lst) if lst.size == 0 => {
        unit.error(p.pos, "No top-level definition found.")
        None
      }

      case PackageDef(name, lst) if lst.size > 1 => {
        unit.error(lst(1).pos, "Too many top-level definitions.")
        None
      }

      case PackageDef(name, lst) => {
        assert(lst.size == 1)
        lst(0) match {
          case ExObjectDef(n, templ) => Some(Program(name.toString, extractObject(n.toString, templ)))
          case other @ _ => unit.error(other.pos, "Expected: top-level single object.")
          None
        }
      }
    }

    // Extraction of the expressions.

//    (new ForeachTreeTraverser(trav)).traverse(unit.body)
    stopIfErrors

    program.get
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

//  def findContracts(tree: Tree): Unit = tree match {
//    case DefDef(/*mods*/ _, name, /*tparams*/ _, /*vparamss*/ _, /*tpt*/ _, body) => {
//      var realBody = body
//      var reqCont: Option[Tree] = None
//      var ensCont: Option[Function] = None
//
//      body match {
//        case EnsuredExpression(body2, contract) => realBody = body2; ensCont = Some(contract)
//        case _ => ;
//      }
//
//      realBody match {
//        case RequiredExpression(body3, contract) => realBody = body3; reqCont = Some(contract)
//        case _ => ;
//      }
//
//      println("In: " + name) 
//      println("  Requires clause: " + reqCont)
//      println("  Ensures  clause: " + ensCont)
//      println("  Body:            " + realBody)
//    }
//
//    case _ => ;
//  }

}
