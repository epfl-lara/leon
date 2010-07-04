package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

class Z3Solver(reporter: Reporter) extends Solver(reporter) {
  val description = "Z3 Solver"
  override val shortDescription = "Z3"

  // this is fixed
  private val z3cfg = new Z3Config()
  z3cfg.setParamValue("MODEL", "true")

  // we restart Z3 for each new program
  private var z3: Z3Context = null
  private var program: Program = null
  private var neverInitialized = true

  override def setProgram(prog: Program) : Unit = {
    program = prog
    if(neverInitialized) {
      neverInitialized = false
      z3 = new Z3Context(z3cfg)
    } else {
      z3.delete
      z3 = new Z3Context(z3cfg)
    }
    prepareSorts
  }

  private var intSort : Z3Sort  = null
  private var boolSort : Z3Sort = null
  private var adtSorts : Map[ClassTypeDef, Z3Sort] = Map.empty
  private var adtTesters : Map[CaseClassDef, Z3FuncDecl] = Map.empty
  private var adtConstructors : Map[CaseClassDef, Z3FuncDecl] = Map.empty
  private var adtFieldSelectors : Map[Identifier,Z3FuncDecl] = Map.empty

  case class UntranslatableTypeException(msg: String) extends Exception(msg)
  private def prepareSorts : Unit = {
    import Z3Context.{ADTSortReference,RecursiveType,RegularSort}
    // NOTE THAT abstract classes that extend abstract classes are not
    // currently supported in the translation
    intSort  = z3.mkIntSort
    boolSort = z3.mkBoolSort

    val roots = program.mainObject.getClassHierarchyRoots
    val indexMap: Map[ClassTypeDef,Int] = Map(roots.zipWithIndex: _*)
    //println("indexMap: " + indexMap)

    def typeToSortRef(tt: TypeTree) : ADTSortReference = tt match {
      case BooleanType => RegularSort(boolSort)
      case Int32Type => RegularSort(intSort)
      case AbstractClassType(d) => RecursiveType(indexMap(d))
      case CaseClassType(d) => indexMap.get(d) match {
        case Some(i) => RecursiveType(i)
        case None => RecursiveType(indexMap(d.parent.get))
      }
      case _ => throw UntranslatableTypeException("Can't handle type " + tt)
    }

    val childrenLists: Seq[List[CaseClassDef]] = roots.map(_ match {
      case c: CaseClassDef => Nil
      case a: AbstractClassDef => a.knownChildren.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef]).toList
    })
    //println("children lists: " + childrenLists.toList.mkString("\n"))

    val rootsAndChildren = (roots zip childrenLists)

    val defs = rootsAndChildren.map(p => {
      val (root, childrenList) = p

      root match {
        case c: CaseClassDef => {
          // we create a recursive type with exactly one constructor
          (c.id.name, List(c.id.name), List(c.fields.map(f => (f.id.name, typeToSortRef(f.tpe)))))
        }
        case a: AbstractClassDef => {
          (a.id.name, childrenList.map(ccd => ccd.id.name), childrenList.map(ccd => ccd.fields.map(f => (f.id.name, typeToSortRef(f.tpe)))))
        } 
      }
    })

    //println(defs)
    // everything should be alright now...
    val resultingZ3Info = z3.mkADTSorts(defs)

    adtSorts = Map.empty
    adtTesters = Map.empty
    adtConstructors = Map.empty
    adtFieldSelectors = Map.empty

    for((z3Inf, (root, childrenList)) <-(resultingZ3Info zip rootsAndChildren)) {
      adtSorts += (root -> z3Inf._1)
      assert(childrenList.size == z3Inf._2.size)
      for((child,(consFun,testFun)) <- childrenList zip (z3Inf._2 zip z3Inf._3)) {
        adtTesters += (child -> testFun)
        adtConstructors += (child -> consFun)
      }
      for((child,fieldFuns) <- childrenList zip z3Inf._4) {
        assert(child.fields.size == fieldFuns.size)
        for((fid,selFun) <- (child.fields.map(_.id) zip fieldFuns)) {
          adtFieldSelectors += (fid -> selFun)
        }
      }
    }
    // ...and now everything should be in there...
  }

  def solve(vc: Expr) : Option[Boolean] = {
    if(neverInitialized) {
        reporter.error("Z3 Solver was not initialized with a PureScala Program.")
        None
    }
    val result = toZ3Formula(z3, negate(vc)) match {
      case None => None // means it could not be translated
      case Some(z3f) => {
        z3.push
        z3.assertCnstr(z3f)
        //z3.print
        val actualResult = (z3.checkAndGetModel() match {
          case (Some(true),m) => {
            reporter.error("There's a bug! Here's a model for a counter-example:")
            m.print
            Some(false)
          }
          case (Some(false),_) => Some(true)
          case (None,_) => {
            reporter.error("Z3 couldn't run properly or does not know the answer :(")
            None
          }
        })
        z3.pop(1) 
        actualResult
      }
    }
    result
  }

  private def toZ3Formula(z3: Z3Context, expr: Expr) : Option[Z3AST] = {
    class CantTranslateException extends Exception

    // because we create identifiers the first time we see them, this is
    // convenient.
    var z3Vars: Map[Identifier,Z3AST] = Map.empty

    def rec(ex: Expr) : Z3AST = ex match {
      case Let(i,e,b) => {
        z3Vars = z3Vars + (i -> rec(e))
        rec(b)
      }
      case v @ Variable(id) => z3Vars.get(id) match {
        case Some(ast) => ast
        case None => {
          val newAST = v.getType match {
            case Int32Type => z3.mkConst(z3.mkStringSymbol(id.name), intSort)
            case BooleanType => z3.mkConst(z3.mkStringSymbol(id.name), boolSort)
            case CaseClassType(cd) => {
              val ccSort = if(cd.hasParent) {
                adtSorts(cd.parent.get)
              } else {
                adtSorts(cd)
              }
              z3.mkConst(z3.mkStringSymbol(id.name), ccSort)
            }
            case _ => {
              reporter.warning("Unsupported type in Z3 transformation: " + v.getType)
              throw new CantTranslateException
            }
          }
          z3Vars = z3Vars + (id -> newAST)
          newAST
        }
      } 
      case IfExpr(c,t,e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec(_)) : _*)
      case Or(exs) => z3.mkOr(exs.map(rec(_)) : _*)
      case Implies(l,r) => z3.mkImplies(rec(l), rec(r))
      case Iff(l,r) => z3.mkIff(rec(l), rec(r))
      case Not(Iff(l,r)) => z3.mkXor(rec(l), rec(r))   
      case Not(Equals(l,r)) => z3.mkDistinct(rec(l),rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case IntLiteral(v) => z3.mkInt(v, intSort)
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l,r) => z3.mkEq(rec(l),rec(r))
      case Plus(l,r) => z3.mkAdd(rec(l), rec(r))
      case Minus(l,r) => z3.mkSub(rec(l), rec(r))
      case Times(l,r) => z3.mkMul(rec(l), rec(r))
      case Division(l,r) => z3.mkDiv(rec(l), rec(r))
      case UMinus(e) => z3.mkUnaryMinus(rec(e))
      case LessThan(l,r) => z3.mkLT(rec(l), rec(r)) 
      case LessEquals(l,r) => z3.mkLE(rec(l), rec(r)) 
      case GreaterThan(l,r) => z3.mkGT(rec(l), rec(r)) 
      case GreaterEquals(l,r) => z3.mkGE(rec(l), rec(r)) 
      case c @ CaseClass(cd, args) => {
        val constructor = adtConstructors(cd)
        constructor(args.map(rec(_)): _*)
      }
      case c @ CaseClassSelector(cc, sel) => {
        val selector = adtFieldSelectors(sel)
        selector(rec(cc))
      }
      case _ => {
        reporter.warning("Can't handle this in translation to Z3: " + ex)
        throw new CantTranslateException
      }
    }
    
    try {
      Some(rec(expr))
    } catch {
      case e: CantTranslateException => None
    }
  }
}
