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
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._

  def extractCode(unit: CompilationUnit): Program = { 
    import scala.collection.mutable.HashMap

    // register where the symbols where extracted from
    // val symbolDefMap = new HashMap[purescala.Symbols.Symbol,Tree]

    def s2ps(tree: Tree): Expr = toPureScala(unit)(tree) match {
      case Some(ex) => ex
      case None => stopIfErrors; scala.Predef.error("unreachable error.")
    }

    def extractTopLevelDef: ObjectDef = {
      val top = unit.body match {
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
            case ExObjectDef(n, templ) => Some(extractObjectDef(n.toString, templ))
            case other @ _ => unit.error(other.pos, "Expected: top-level single object.")
            None
          }
        }
      }

      stopIfErrors
      top.get
    }

    def extractObjectDef(name: Identifier, tmpl: Template): ObjectDef = {
      // we assume that the template actually corresponds to an object
      // definition. Typically it should have been obtained from the proper
      // extractor (ExObjectDef)

      var classDefs: List[ClassTypeDef] = Nil
      var objectDefs: List[ObjectDef] = Nil
      var funDefs: List[FunDef] = Nil

      tmpl.body.foreach(tree => {
        println("[[[ " + tree + "]]]\n");
        tree match {
        case ExObjectDef(o2, t2) => { objectDefs = extractObjectDef(o2, t2) :: objectDefs }
        case ExAbstractClass(o2) => ;
        case ExConstructorDef() => ;
        case ExMainFunctionDef() => ;
        case ExFunctionDef(n,p,t,b) => { funDefs = extractFunDef(n,p,t,b) :: funDefs }
        case _ => ;
      }})

      // val theSym = new purescala.Symbols.ObjectSymbol(name, classSyms.reverse, objectSyms.reverse)
      // we register the tree associated to the symbol to be able to fill in
      // the rest later
      // symbolDefMap(theSym) = tmpl
      val theDef = new ObjectDef(name, objectDefs.reverse ::: classDefs.reverse ::: funDefs.reverse, Nil)
      theDef
    }

    def extractFunDef(name: Identifier, params: Seq[ValDef], tpt: Tree, body: Tree) = {
      FunDef(name, scalaType2PureScala(unit, false)(tpt), Nil, null, None, None)
    }

    // THE EXTRACTION CODE STARTS HERE
    val topLevelObjDef: ObjectDef = extractTopLevelDef

    stopIfErrors

    val programName: Identifier = unit.body match {
      case PackageDef(name, _) => name.toString
      case _ => "<program>"
    }

    println("Top level sym:")
    println(topLevelObjDef)


    //Program(programName, ObjectDef("Object", Nil, Nil))
    Program(programName, topLevelObjDef)
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

  private def scalaType2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Tree): funcheck.purescala.TypeTrees.TypeTree = {
    tree match {
      case tt: TypeTree if tt.tpe == IntClass.tpe => Int32Type

      case _ => {
        if(!silent) {
          unit.error(tree.pos, "Could not extract type as PureScala.")
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
