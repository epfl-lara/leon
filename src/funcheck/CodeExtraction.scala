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

  private val varSubsts: scala.collection.mutable.Map[Identifier,Function0[Expr]] = scala.collection.mutable.Map.empty[Identifier,Function0[Expr]]

  def extractCode(unit: CompilationUnit): Program = { 
    import scala.collection.mutable.HashMap

    def s2ps(tree: Tree): Expr = toPureScala(unit)(tree) match {
      case Some(ex) => ex
      case None => stopIfErrors; scala.Predef.error("unreachable error.")
    }

    def st2ps(tree: Tree): purescala.TypeTrees.TypeTree = toPureScalaType(unit)(tree) match {
      case Some(tt) => tt
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
        //println("[[[ " + tree + "]]]\n");
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
      var realBody = body
      var reqCont: Option[Expr] = None
      var ensCont: Option[Expr] = None

      val ps = params.map(p => VarDecl(p.name.toString, st2ps(p.tpt)))

      realBody match {
        case ExEnsuredExpression(body2, resId, contract) => {
          varSubsts(resId) = (() => ResultVariable())
          val c1 = s2ps(contract)
          varSubsts.remove(resId)
          realBody = body2
          ensCont = Some(c1)
        }
        case _ => ;
      }

      realBody match {
        case ExRequiredExpression(body3, contract) => {
          realBody = body3
          reqCont = Some(s2ps(contract))
        }
        case _ => ;
      }
      
      FunDef(name, st2ps(tpt), ps, s2ps(realBody), reqCont, ensCont)
    }

    // THE EXTRACTION CODE STARTS HERE
    val topLevelObjDef: ObjectDef = extractTopLevelDef

    stopIfErrors

    val programName: Identifier = unit.body match {
      case PackageDef(name, _) => name.toString
      case _ => "<program>"
    }

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

  def toPureScalaType(unit: CompilationUnit)(typeTree: Tree): Option[purescala.TypeTrees.TypeTree] = {
    try {
      Some(scalaType2PureScala(unit, false)(typeTree))
    } catch {
      case ImpureCodeEncounteredException(_) => None
    }
  }

  /** Forces conversion from scalac AST to purescala AST, throws an Exception
   * if impossible. If not in 'silent mode', non-pure AST nodes are reported as
   * errors. */
  private def scala2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Tree): Expr = {
    def rec(tr: Tree): Expr = tr match {
      case ExInt32Literal(v) => IntLiteral(v)
      case ExBooleanLiteral(v) => BooleanLiteral(v)
      case ExIdentifier(id,tpt) => varSubsts.get(id) match {
        case Some(fun) => fun()
        case None => Variable(id)
      }
      case ExAnd(l, r) => And(rec(l), rec(r))
      case ExPlus(l, r) => Plus(rec(l), rec(r))
      case ExEquals(l, r) => Equals(rec(l), rec(r))
      case ExGreaterThan(l, r) => GreaterThan(rec(l), rec(r))
      case ExGreaterEqThan(l, r) => GreaterEquals(rec(l), rec(r))
      case ExLessThan(l, r) => LessThan(rec(l), rec(r))
      case ExLessEqThan(l, r) => LessEquals(rec(l), rec(r))
  
      // default behaviour is to complain :)
      case _ => {
        if(!silent) {
          println(tr)
          unit.error(tree.pos, "Could not extract as PureScala.")
        }
        throw ImpureCodeEncounteredException(tree)
      }
    }

    rec(tree)
  }

  private def scalaType2PureScala(unit: CompilationUnit, silent: Boolean)(tree: Tree): purescala.TypeTrees.TypeTree = {
    tree match {
      case tt: TypeTree if tt.tpe == IntClass.tpe => Int32Type
      case tt: TypeTree if tt.tpe == BooleanClass.tpe => BooleanType

      case _ => {
        if(!silent) {
          unit.error(tree.pos, "Could not extract type as PureScala.")
        }
        throw ImpureCodeEncounteredException(tree)
      }
    }
  }
}
