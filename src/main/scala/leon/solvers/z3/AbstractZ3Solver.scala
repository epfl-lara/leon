/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package solvers.z3

import leon.utils._

import z3.scala._
import solvers._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import xlang.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait AbstractZ3Solver extends SolverFactory[Solver] {
  val context : LeonContext
  val program : Program

  protected[z3] val reporter : Reporter = context.reporter

  context.interruptManager.registerForInterrupts(this)

  private[this] var freed = false
  val traceE = new Exception()

  override def finalize() {
    if (!freed) {
      println("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      traceE.printStackTrace()
      free()
    }
  }

  class CantTranslateException(t: Z3AST) extends Exception("Can't translate from Z3 tree: " + t)

  protected[leon] val z3cfg : Z3Config
  protected[leon] var z3 : Z3Context    = null

  override def free() {
    freed = true
    super.free()
    if (z3 ne null) {
      z3.delete()
      z3 = null;
    }
  }

  override def interrupt() {
    super.interrupt()
    if(z3 ne null) {
      z3.interrupt
    }
  }

  protected[leon] def prepareFunctions : Unit
  protected[leon] def functionDefToDecl(funDef: FunDef) : Z3FuncDecl
  protected[leon] def functionDeclToDef(decl: Z3FuncDecl) : FunDef
  protected[leon] def isKnownDecl(decl: Z3FuncDecl) : Boolean

  // Lifting of common parts starts here
  protected[leon] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[leon] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty

  protected[leon] var intSort: Z3Sort = null
  protected[leon] var boolSort: Z3Sort = null
  protected[leon] var setSorts: Map[TypeTree, Z3Sort] = Map.empty
  protected[leon] var mapSorts: Map[TypeTree, Z3Sort] = Map.empty
  protected[leon] var unitSort: Z3Sort = null
  protected[leon] var unitValue: Z3AST = null

  protected[leon] var funSorts: Map[TypeTree, Z3Sort] = Map.empty
  protected[leon] var funDomainConstructors: Map[TypeTree, Z3FuncDecl] = Map.empty
  protected[leon] var funDomainSelectors: Map[TypeTree, Seq[Z3FuncDecl]] = Map.empty

  protected[leon] var tupleSorts: Map[TypeTree, Z3Sort] = Map.empty
  protected[leon] var tupleConstructors: Map[TypeTree, Z3FuncDecl] = Map.empty
  protected[leon] var tupleSelectors: Map[TypeTree, Seq[Z3FuncDecl]] = Map.empty

  protected[leon] var arraySorts: Map[TypeTree, Z3Sort] = Map.empty
  protected[leon] var arrayTupleCons: Map[TypeTree, Z3FuncDecl] = Map.empty
  protected[leon] var arrayTupleSelectorArray: Map[TypeTree, Z3FuncDecl] = Map.empty
  protected[leon] var arrayTupleSelectorLength: Map[TypeTree, Z3FuncDecl] = Map.empty

  protected[leon] var reverseTupleConstructors: Map[Z3FuncDecl, TupleType] = Map.empty
  protected[leon] var reverseTupleSelectors: Map[Z3FuncDecl, (TupleType, Int)] = Map.empty

  protected[leon] var intSetMinFun: Z3FuncDecl = null
  protected[leon] var intSetMaxFun: Z3FuncDecl = null
  protected[leon] var setCardFuns: Map[TypeTree, Z3FuncDecl] = Map.empty
  protected[leon] var adtSorts: Map[ClassTypeDef, Z3Sort] = Map.empty
  protected[leon] var fallbackSorts: Map[TypeTree, Z3Sort] = Map.empty

  protected[leon] var adtTesters: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  protected[leon] var adtConstructors: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  protected[leon] var adtFieldSelectors: Map[Identifier, Z3FuncDecl] = Map.empty

  protected[leon] var reverseADTTesters: Map[Z3FuncDecl, CaseClassDef] = Map.empty
  protected[leon] var reverseADTConstructors: Map[Z3FuncDecl, CaseClassDef] = Map.empty
  protected[leon] var reverseADTFieldSelectors: Map[Z3FuncDecl, (CaseClassDef,Identifier)] = Map.empty

  protected[leon] val mapRangeSorts: MutableMap[TypeTree, Z3Sort] = MutableMap.empty
  protected[leon] val mapRangeSomeConstructors: MutableMap[TypeTree, Z3FuncDecl] = MutableMap.empty
  protected[leon] val mapRangeNoneConstructors: MutableMap[TypeTree, Z3FuncDecl] = MutableMap.empty
  protected[leon] val mapRangeSomeTesters: MutableMap[TypeTree, Z3FuncDecl] = MutableMap.empty
  protected[leon] val mapRangeNoneTesters: MutableMap[TypeTree, Z3FuncDecl] = MutableMap.empty
  protected[leon] val mapRangeValueSelectors: MutableMap[TypeTree, Z3FuncDecl] = MutableMap.empty

  private var counter = 0
  private object nextIntForSymbol {
    def apply(): Int = {
      val res = counter
      counter = counter + 1
      res
    }
  }

  var isInitialized = false
  protected[leon] def initZ3() {
    if (!isInitialized) {
      val initTime     = new Timer().start
      counter = 0

      z3 = new Z3Context(z3cfg)

      prepareSorts
      prepareFunctions

      isInitialized = true

      initTime.stop
      context.timers.get("Z3Solver init") += initTime
    }
  }

  protected[leon] def restartZ3() {
    isInitialized = false

    initZ3()

    exprToZ3Id = Map.empty
    z3IdToExpr = Map.empty
  }

  protected[leon] def mapRangeSort(toType : TypeTree) : Z3Sort = mapRangeSorts.get(toType) match {
    case Some(z3sort) => z3sort
    case None => {
      import Z3Context.{ADTSortReference, RecursiveType, RegularSort}

      intSort = z3.mkIntSort
      boolSort = z3.mkBoolSort

      def typeToSortRef(tt: TypeTree): ADTSortReference = tt match {
        case BooleanType => RegularSort(boolSort)
        case Int32Type => RegularSort(intSort)
        case AbstractClassType(d) => RegularSort(adtSorts(d))
        case CaseClassType(d) => RegularSort(adtSorts(d))
        case SetType(d) => RegularSort(setSorts(d))
        case mt @ MapType(d,r) => RegularSort(mapSorts(mt))
        case _ => throw UntranslatableTypeException("Can't handle type " + tt)
      }

      val z3info = z3.mkADTSorts(
        Seq(
          (
            toType.toString + "Option",
            Seq(toType.toString + "Some", toType.toString + "None"),
            Seq(
              Seq(("value", typeToSortRef(toType))),
              Seq()
            )
          )
        )
      )

      z3info match {
        case Seq((optionSort, Seq(someCons, noneCons), Seq(someTester, noneTester), Seq(Seq(valueSelector), Seq()))) =>
          mapRangeSorts += ((toType, optionSort))
          mapRangeSomeConstructors += ((toType, someCons))
          mapRangeNoneConstructors += ((toType, noneCons))
          mapRangeSomeTesters += ((toType, someTester))
          mapRangeNoneTesters += ((toType, noneTester))
          mapRangeValueSelectors += ((toType, valueSelector))
          optionSort
      }
    }
  }

  case class UntranslatableTypeException(msg: String) extends Exception(msg)
  // Prepares some of the Z3 sorts, but *not* the tuple sorts; these are created on-demand.
  private def prepareSorts: Unit = {
    import Z3Context.{ADTSortReference, RecursiveType, RegularSort}
    // NOTE THAT abstract classes that extend abstract classes are not
    // currently supported in the translation
    
    intSort = z3.mkIntSort
    boolSort = z3.mkBoolSort
    setSorts = Map.empty
    setCardFuns = Map.empty

    //unitSort = z3.mkUninterpretedSort("unit")
    //unitValue = z3.mkFreshConst("Unit", unitSort)
    //val bound = z3.mkBound(0, unitSort)
    //val eq = z3.mkEq(bound, unitValue)
    //val decls = Seq((z3.mkFreshStringSymbol("u"), unitSort))
    //val unitAxiom = z3.mkForAll(0, Seq(), decls, eq)
    //println(unitAxiom)
    //println(unitValue)
    //z3.assertCnstr(unitAxiom)
    val Seq((us, Seq(unitCons), Seq(unitTester), _)) = z3.mkADTSorts(
      Seq(
        (
          "Unit",
          Seq("Unit"),
          Seq(Seq())
        )
      )
    )
    unitSort = us
    unitValue = unitCons()

    val intSetSort = typeToSort(SetType(Int32Type))
    intSetMinFun = z3.mkFreshFuncDecl("setMin", Seq(intSetSort), intSort)
    intSetMaxFun = z3.mkFreshFuncDecl("setMax", Seq(intSetSort), intSort)

    val roots = program.classHierarchyRoots
    val indexMap: Map[ClassTypeDef, Int] = Map(roots.zipWithIndex: _*)
    //println("indexMap: " + indexMap)

    def typeToSortRef(tt: TypeTree): ADTSortReference = tt match {
      // case BooleanType => RegularSort(boolSort)
      // case Int32Type => RegularSort(intSort)
      case AbstractClassType(d) => RecursiveType(indexMap(d))
      case CaseClassType(d) => indexMap.get(d) match {
        case Some(i) => RecursiveType(i)
        case None => RecursiveType(indexMap(d.parent.get))
      }
      // case _ => throw UntranslatableTypeException("Can't handle type " + tt)
      case _ => RegularSort(typeToSort(tt))
    }

    val childrenLists: Seq[List[CaseClassDef]] = roots.map(_ match {
      case c: CaseClassDef => List(c)
      case a: AbstractClassDef => a.knownChildren.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef]).toList
    })
    //println("children lists: " + childrenLists.toList.mkString("\n"))

    val rootsAndChildren = (roots zip childrenLists)

    val defs = rootsAndChildren.map(p => {
      val (root, childrenList) = p

      root match {
        case c: CaseClassDef => {
          // we create a recursive type with exactly one constructor
          (c.id.uniqueName, List(c.id.uniqueName), List(c.fields.map(f => (f.id.uniqueName, typeToSortRef(f.tpe)))))
        }
        case a: AbstractClassDef => {
          (a.id.uniqueName, childrenList.map(ccd => ccd.id.uniqueName), childrenList.map(ccd => ccd.fields.map(f => (f.id.uniqueName, typeToSortRef(f.tpe)))))
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
    reverseADTTesters = Map.empty
    reverseADTConstructors = Map.empty
    reverseADTFieldSelectors = Map.empty

    for ((z3Inf, (root, childrenList)) <- (resultingZ3Info zip rootsAndChildren)) {
      adtSorts += (root -> z3Inf._1)
      assert(childrenList.size == z3Inf._2.size)
      for ((child, (consFun, testFun)) <- childrenList zip (z3Inf._2 zip z3Inf._3)) {
        adtTesters += (child -> testFun)
        adtConstructors += (child -> consFun)
      }
      for ((child, fieldFuns) <- childrenList zip z3Inf._4) {
        assert(child.fields.size == fieldFuns.size)
        for ((fid, selFun) <- (child.fields.map(_.id) zip fieldFuns)) {
          adtFieldSelectors += (fid -> selFun)
          reverseADTFieldSelectors += (selFun -> (child, fid))
        }
      }
    }

    reverseADTTesters = adtTesters.map(_.swap)
    reverseADTConstructors = adtConstructors.map(_.swap)
    // ...and now everything should be in there...
  }

  // assumes prepareSorts has been called....
  protected[leon] def typeToSort(tt: TypeTree): Z3Sort = tt match {
    case Int32Type => intSort
    case BooleanType => boolSort
    case UnitType => unitSort
    case AbstractClassType(cd) => adtSorts(cd)
    case CaseClassType(cd) => {
      if (cd.hasParent) {
        adtSorts(cd.parent.get)
      } else {
        adtSorts(cd)
      }
    }
    case SetType(base) => setSorts.get(base) match {
      case Some(s) => s
      case None => {
        val newSetSort = z3.mkSetSort(typeToSort(base))
        setSorts = setSorts + (base -> newSetSort)
        val newCardFun = z3.mkFreshFuncDecl("card", Seq(newSetSort), intSort)
        setCardFuns = setCardFuns + (base -> newCardFun)
        newSetSort
      }
    }
    case mt @ MapType(fromType, toType) => mapSorts.get(mt) match {
      case Some(s) => s
      case None => {
        val fromSort = typeToSort(fromType)
        val toSort = mapRangeSort(toType)
        val ms = z3.mkArraySort(fromSort, toSort)
        mapSorts += ((mt, ms))
        ms
      }
    }
    case at @ ArrayType(base) => arraySorts.get(at) match {
      case Some(s) => s
      case None => {
        val intSort = typeToSort(Int32Type)
        val toSort = typeToSort(base)
        val as = z3.mkArraySort(intSort, toSort)
        val tupleSortSymbol = z3.mkFreshStringSymbol("Array")
        val (arrayTupleSort, arrayTupleCons_, Seq(arrayTupleSelectorArray_, arrayTupleSelectorLength_)) = z3.mkTupleSort(tupleSortSymbol, as, intSort)
        arraySorts += (at -> arrayTupleSort)
        arrayTupleCons += (at -> arrayTupleCons_)
        arrayTupleSelectorArray += (at -> arrayTupleSelectorArray_)
        arrayTupleSelectorLength += (at -> arrayTupleSelectorLength_)
        arrayTupleSort
      }
    }
    case tt @ TupleType(tpes) => tupleSorts.get(tt) match {
      case Some(s) => s
      case None => {
        val tpesSorts = tpes.map(typeToSort)
        val sortSymbol = z3.mkFreshStringSymbol("Tuple")
        val (tupleSort, consTuple, projsTuple) = z3.mkTupleSort(sortSymbol, tpesSorts: _*)
        tupleSorts += (tt -> tupleSort)
        tupleConstructors += (tt -> consTuple)
        reverseTupleConstructors += (consTuple -> tt)
        tupleSelectors += (tt -> projsTuple)
        projsTuple.zipWithIndex.foreach{ case (proj, i) => reverseTupleSelectors += (proj -> (tt, i)) }
        tupleSort
      }
    }
    case other => fallbackSorts.get(other) match {
      case Some(s) => s
      case None => {
        reporter.warning("Resorting to uninterpreted type for : " + other)
        val symbol = z3.mkIntSymbol(nextIntForSymbol())
        val newFBSort = z3.mkUninterpretedSort(symbol)
        fallbackSorts = fallbackSorts + (other -> newFBSort)
        newFBSort
      }
    }
  }

  protected[leon] def toZ3Formula(expr: Expr, initialMap: Map[Identifier,Z3AST] = Map.empty) : Option[Z3AST] = {
    class CantTranslateException extends Exception

    val varsInformula: Set[Identifier] = variablesOf(expr)

    var z3Vars: Map[Identifier,Z3AST] = if(!initialMap.isEmpty) {
      initialMap
    } else {
      // FIXME TODO pleeeeeeeease make this cleaner. Ie. decide what set of
      // variable has to remain in a map etc.
      exprToZ3Id.filter(p => p._1.isInstanceOf[Variable]).map(p => (p._1.asInstanceOf[Variable].id -> p._2))
    }

    def rec(ex: Expr): Z3AST = { 
      //println("Stacking up call for:")
      //println(ex)
      val recResult = (ex match {
        case tu @ Tuple(args) => {
          // This call is required, because the Z3 sort may not have been generated yet.
          // If it has, it's just a map lookup and instant return.
          typeToSort(tu.getType)
          val constructor = tupleConstructors(tu.getType)
          constructor(args.map(rec(_)): _*)
        }
        case ts @ TupleSelect(tu, i) => {
          // See comment above for similar code.
          typeToSort(tu.getType)
          val selector = tupleSelectors(tu.getType)(i-1)
          selector(rec(tu))
        }
        case Let(i, e, b) => {
          val re = rec(e)
          z3Vars = z3Vars + (i -> re)
          val rb = rec(b)
          z3Vars = z3Vars - i
          rb
        }
        case Waypoint(_, e) => rec(e)
        case e @ Error(_) => {
          val tpe = e.getType
          val newAST = z3.mkFreshConst("errorValue", typeToSort(tpe))
          exprToZ3Id += (e -> newAST)
          z3IdToExpr += (newAST -> e)
          newAST
        }
        case v @ Variable(id) => z3Vars.get(id) match {
          case Some(ast) => ast
          case None => {
            // if (id.isLetBinder) {
            //   scala.sys.error("Error in formula being translated to Z3: identifier " + id + " seems to have escaped its let-definition")
            // }

            // Remove this safety check, since choose() expresions are now
            // translated to non-unrollable variables, that end up here.
            // assert(!this.isInstanceOf[FairZ3Solver], "Trying to convert unknown variable '"+id+"' while using FairZ3")

            val newAST = z3.mkFreshConst(id.uniqueName/*name*/, typeToSort(v.getType))
            z3Vars = z3Vars + (id -> newAST)
            exprToZ3Id += (v -> newAST)
            z3IdToExpr += (newAST -> v)
            newAST
          }
        }

        case ite @ IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
        case And(exs) => z3.mkAnd(exs.map(rec(_)): _*)
        case Or(exs) => z3.mkOr(exs.map(rec(_)): _*)
        case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
        case Iff(l, r) => {
          val rl = rec(l)
          val rr = rec(r)
          // z3.mkIff used to trigger a bug
          // z3.mkAnd(z3.mkImplies(rl, rr), z3.mkImplies(rr, rl))
          z3.mkIff(rl, rr)
        }
        case Not(Iff(l, r)) => z3.mkXor(rec(l), rec(r))
        case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
        case Not(e) => z3.mkNot(rec(e))
        case IntLiteral(v) => z3.mkInt(v, intSort)
        case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
        case UnitLiteral => unitValue
        case Equals(l, r) => z3.mkEq(rec(l), rec(r))
        case Plus(l, r) => z3.mkAdd(rec(l), rec(r))
        case Minus(l, r) => z3.mkSub(rec(l), rec(r))
        case Times(l, r) => z3.mkMul(rec(l), rec(r))
        case Division(l, r) => z3.mkDiv(rec(l), rec(r))
        case Modulo(l, r) => z3.mkMod(rec(l), rec(r))
        case UMinus(e) => z3.mkUnaryMinus(rec(e))
        case LessThan(l, r) => z3.mkLT(rec(l), rec(r))
        case LessEquals(l, r) => z3.mkLE(rec(l), rec(r))
        case GreaterThan(l, r) => z3.mkGT(rec(l), rec(r))
        case GreaterEquals(l, r) => z3.mkGE(rec(l), rec(r))
        case c @ CaseClass(cd, args) => {
          val constructor = adtConstructors(cd)
          constructor(args.map(rec(_)): _*)
        }
        case c @ CaseClassSelector(_, cc, sel) => {
          val selector = adtFieldSelectors(sel)
          selector(rec(cc))
        }
        case c @ CaseClassInstanceOf(ccd, e) => {
          val tester = adtTesters(ccd)
          tester(rec(e))
        }
        case f @ FunctionInvocation(fd, args) => {
          z3.mkApp(functionDefToDecl(fd), args.map(rec(_)): _*)
        }
        
        case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
        case ElementOfSet(e, s) => z3.mkSetSubset(z3.mkSetAdd(z3.mkEmptySet(typeToSort(e.getType)), rec(e)), rec(s))
        case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
        case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))
        case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
        case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
        case f @ FiniteSet(elems) => elems.foldLeft(z3.mkEmptySet(typeToSort(f.getType.asInstanceOf[SetType].base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))
        case SetCardinality(s) => {
          val rs = rec(s)
          setCardFuns(s.getType.asInstanceOf[SetType].base)(rs)
        }
        case SetMin(s) => intSetMinFun(rec(s))
        case SetMax(s) => intSetMaxFun(rec(s))
        case f @ FiniteMap(elems) => f.getType match {
          case tpe@MapType(fromType, toType) =>
            typeToSort(tpe) //had to add this here because the mapRangeNoneConstructors was not yet constructed...
            val fromSort = typeToSort(fromType)
            val toSort = typeToSort(toType)
            elems.foldLeft(z3.mkConstArray(fromSort, mapRangeNoneConstructors(toType)())){ case (ast, (k,v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(toType)(rec(v))) }
          case errorType => scala.sys.error("Unexpected type for finite map: " + (ex, errorType))
        }
        case mg @ MapGet(m,k) => m.getType match {
          case MapType(fromType, toType) =>
            val selected = z3.mkSelect(rec(m), rec(k))
            mapRangeValueSelectors(toType)(selected)
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapUnion(m1,m2) => m1.getType match {
          case MapType(ft, tt) => m2 match {
            case FiniteMap(ss) =>
              ss.foldLeft(rec(m1)){
                case (ast, (k, v)) => z3.mkStore(ast, rec(k), mapRangeSomeConstructors(tt)(rec(v)))
              }
            case _ => scala.sys.error("map updates can only be applied with concrete map instances")
          }
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case MapIsDefinedAt(m,k) => m.getType match {
          case MapType(ft, tt) => z3.mkDistinct(z3.mkSelect(rec(m), rec(k)), mapRangeNoneConstructors(tt)())
          case errorType => scala.sys.error("Unexpected type for map: " + (ex, errorType))
        }
        case fill @ ArrayFill(length, default) => {
          val at@ArrayType(base) = fill.getType
          typeToSort(at)
          val cons = arrayTupleCons(at)
          val ar = z3.mkConstArray(typeToSort(base), rec(default))
          val res = cons(ar, rec(length))
          res
        }
        case ArraySelect(a, index) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val res = z3.mkSelect(getArray(ar), rec(index))
          res
        }
        case ArrayUpdated(a, index, newVal) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getArray = arrayTupleSelectorArray(a.getType)
          val getLength = arrayTupleSelectorLength(a.getType)
          val cons = arrayTupleCons(a.getType)
          val store = z3.mkStore(getArray(ar), rec(index), rec(newVal))
          val res = cons(store, getLength(ar))
          res
        }
        case ArrayLength(a) => {
          typeToSort(a.getType)
          val ar = rec(a)
          val getLength = arrayTupleSelectorLength(a.getType)
          val res = getLength(ar)
          res
        }

        case arr @ FiniteArray(exprs) => {
          val ArrayType(innerType) = arr.getType
          val arrayType = arr.getType
          val a: Expr = ArrayFill(IntLiteral(exprs.length), simplestValue(innerType)).setType(arrayType)
          val u = exprs.zipWithIndex.foldLeft(a)((array, expI) => ArrayUpdated(array, IntLiteral(expI._2), expI._1).setType(arrayType))
          rec(u)
        }
        case Distinct(exs) => z3.mkDistinct(exs.map(rec(_)): _*)
  
        case _ => {
          reporter.warning("Can't handle this in translation to Z3: " + ex)
          throw new CantTranslateException
        }
      })
      recResult
    }

    try {
      val res = Some(rec(expr))
      res
    } catch {
      case e: CantTranslateException => None
    }
  }

  protected[leon] def fromZ3Formula(model: Z3Model, tree : Z3AST, expectedType: Option[TypeTree] = None) : Expr = {
    def rec(t: Z3AST, expType: Option[TypeTree] = None) : Expr = expType match {
      case _ if z3IdToExpr contains t => z3IdToExpr(t)

      case Some(MapType(kt,vt)) => 
        model.getArrayValue(t) match {
          case None => throw new CantTranslateException(t)
          case Some((map, elseValue)) => 
            val singletons: Seq[(Expr, Expr)] = map.map(e => (e, z3.getASTKind(e._2))).collect {
              case ((index, value), Z3AppAST(someCons, arg :: Nil)) if someCons == mapRangeSomeConstructors(vt) => (rec(index, Some(kt)), rec(arg, Some(vt)))
            }.toSeq
            FiniteMap(singletons).setType(expType.get)
        }
      case Some(SetType(dt)) => 
        model.getSetValue(t) match {
          case None => throw new CantTranslateException(t)
          case Some(set) => {
            val elems = set.map(e => rec(e, Some(dt)))
            FiniteSet(elems.toSeq).setType(expType.get)
          }
        }
      case Some(ArrayType(dt)) => {
        val Z3AppAST(decl, args) = z3.getASTKind(t)
        assert(args.size == 2)
        val IntLiteral(length) = rec(args(1), Some(Int32Type))
        val array = model.getArrayValue(args(0)) match {
          case None => throw new CantTranslateException(t)
          case Some((map, elseValue)) => {
            val exprs = map.foldLeft((1 to length).map(_ => rec(elseValue, Some(dt))).toSeq)((acc, p) => {
              val IntLiteral(index) = rec(p._1, Some(Int32Type))
              if(index >= 0 && index < length)
                acc.updated(index, rec(p._2, Some(dt)))
              else acc
            })
            FiniteArray(exprs)
          }
        }
        array
      }
      case other => 
        if(t == unitValue) 
          UnitLiteral
        else z3.getASTKind(t) match {
          case Z3AppAST(decl, args) => {
            val argsSize = args.size
            if(argsSize == 0 && z3IdToExpr.isDefinedAt(t)) {
              val toRet = z3IdToExpr(t)
              // println("Map says I should replace " + t + " by " + toRet)
              toRet
            } else if(isKnownDecl(decl)) {
              val fd = functionDeclToDef(decl)
              assert(fd.args.size == argsSize)
              FunctionInvocation(fd, (args zip fd.args).map(p => rec(p._1,Some(p._2.tpe))))
            } else if(argsSize == 1 && reverseADTTesters.isDefinedAt(decl)) {
              CaseClassInstanceOf(reverseADTTesters(decl), rec(args(0)))
            } else if(argsSize == 1 && reverseADTFieldSelectors.isDefinedAt(decl)) {
              val (ccd, fid) = reverseADTFieldSelectors(decl)
              CaseClassSelector(ccd, rec(args(0)), fid)
            } else if(reverseADTConstructors.isDefinedAt(decl)) {
              val ccd = reverseADTConstructors(decl)
              assert(argsSize == ccd.fields.size)
              CaseClass(ccd, (args zip ccd.fields).map(p => rec(p._1, Some(p._2.tpe))))
            } else if(reverseTupleConstructors.isDefinedAt(decl)) {
              val TupleType(subTypes) = reverseTupleConstructors(decl)
              val rargs = args.zip(subTypes).map(p => rec(p._1, Some(p._2)))
              Tuple(rargs)
            } else {
              import Z3DeclKind._
              val rargs = args.map(rec(_))
              z3.getDeclKind(decl) match {
                case OpTrue => BooleanLiteral(true)
                case OpFalse => BooleanLiteral(false)
                case OpEq => Equals(rargs(0), rargs(1))
                case OpITE =>
                  assert(argsSize == 3)
                  val r0 = rargs(0)
                  val r1 = rargs(1)
                  val r2 = rargs(2)
                  try {
                    IfExpr(r0, r1, r2).setType(leastUpperBound(r1.getType, r2.getType).get)
                  } catch {
                    case e: Throwable =>
                      println("I was asking for lub because of this.")
                      println(t)
                      println("which was translated as")
                      println(IfExpr(r0,r1,r2))
                      throw e
                  }

                case OpAnd => And(rargs)
                case OpOr => Or(rargs)
                case OpIff => Iff(rargs(0), rargs(1))
                case OpXor => Not(Iff(rargs(0), rargs(1)))
                case OpNot => Not(rargs(0))
                case OpImplies => Implies(rargs(0), rargs(1))
                case OpLE => LessEquals(rargs(0), rargs(1))
                case OpGE => GreaterEquals(rargs(0), rargs(1))
                case OpLT => LessThan(rargs(0), rargs(1))
                case OpGT => GreaterThan(rargs(0), rargs(1))
                case OpAdd => {
                  assert(argsSize == 2)
                  Plus(rargs(0), rargs(1))
                }
                case OpSub => {
                  assert(argsSize == 2)
                  Minus(rargs(0), rargs(1))
                }
                case OpUMinus => UMinus(rargs(0))
                case OpMul => {
                  assert(argsSize == 2)
                  Times(rargs(0), rargs(1))
                }
                case OpDiv => {
                  assert(argsSize == 2)
                  Division(rargs(0), rargs(1))
                }
                case OpIDiv => {
                  assert(argsSize == 2)
                  Division(rargs(0), rargs(1))
                }
                case OpMod => {
                  assert(argsSize == 2)
                  Modulo(rargs(0), rargs(1))
                }
                case OpAsArray => {
                  assert(argsSize == 0)
                  throw new Exception("encountered OpAsArray")
                }
                case other => {
                  System.err.println("Don't know what to do with this declKind : " + other)
                  System.err.println("The arguments are : " + args)
                  throw new CantTranslateException(t)
                }
              }
            }
          }

          case Z3NumeralAST(Some(v)) => IntLiteral(v)
          case Z3NumeralAST(None) => {
            reporter.info("Cannot read exact model from Z3: Integer does not fit in machine word")
            reporter.info("Exiting procedure now")
            sys.exit(0)
          }
          case other @ _ => {
            System.err.println("Don't know what this is " + other) 
            throw new CantTranslateException(t)
          }
        }
    }
    rec(tree, expectedType)
  }

  // Tries to convert a Z3AST into a *ground* Expr. Doesn't try very hard, because
  //   1) we assume Z3 simplifies ground terms, so why match for +, etc, and
  //   2) we use this precisely in one context, where we know function invocations won't show up, etc.
  protected[leon] def asGround(tree : Z3AST) : Option[Expr] = {
    val e = new Exception("Not ground.")

    def rec(t : Z3AST) : Expr = z3.getASTKind(t) match {
      case Z3AppAST(decl, args) => {
        val argsSize = args.size
        if(isKnownDecl(decl)) {
          val fd = functionDeclToDef(decl)
          FunctionInvocation(fd, args.map(rec))
        } else if(argsSize == 1 && reverseADTTesters.isDefinedAt(decl)) {
          CaseClassInstanceOf(reverseADTTesters(decl), rec(args(0)))
        } else if(argsSize == 1 && reverseADTFieldSelectors.isDefinedAt(decl)) {
          val (ccd, fid) = reverseADTFieldSelectors(decl)
          CaseClassSelector(ccd, rec(args(0)), fid)
        } else if(reverseADTConstructors.isDefinedAt(decl)) {
          val ccd = reverseADTConstructors(decl)
          CaseClass(ccd, args.map(rec))
        } else if(reverseTupleConstructors.isDefinedAt(decl)) {
          Tuple(args.map(rec))
        } else {
          import Z3DeclKind._
          z3.getDeclKind(decl) match {
            case OpTrue => BooleanLiteral(true)
            case OpFalse => BooleanLiteral(false)
            case _ => throw e
          }
        }
      }
      case Z3NumeralAST(Some(v)) => IntLiteral(v)
      case _ => throw e
    }

    try {
      Some(rec(tree))
    } catch {
      case e : Exception => None
    }
  }

  protected[leon] def softFromZ3Formula(model: Z3Model, tree : Z3AST, expectedType: TypeTree) : Option[Expr] = {
    try {
      Some(fromZ3Formula(model, tree, Some(expectedType)))
    } catch {
      case e: CantTranslateException => None
    }
  }

  def idToFreshZ3Id(id: Identifier): Z3AST = {
    z3.mkFreshConst(id.uniqueName, typeToSort(id.getType))
  }

}
