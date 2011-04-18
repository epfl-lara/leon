package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import z3plugins.bapa.{BAPATheory, BAPATheoryEqc, BAPATheoryBubbles}
import z3plugins.instantiator.{AbstractInstantiator,Instantiator}

import scala.collection.mutable.{HashMap => MutableHashMap}

class Z3Solver(val reporter: Reporter) extends Solver(reporter) with AbstractZ3Solver with Z3ModelReconstruction {
  import Settings.useBAPA
  import Settings.{useInstantiator,useFairInstantiator,useAnyInstantiator}

  val description = "Z3 Solver"
  override val shortDescription = "Z3"

  //   type BAPATheoryType = BAPATheory
  //   type BAPATheoryType = BAPATheoryEqc
  type BAPATheoryType = BAPATheoryBubbles

  private val reportUnknownAsSat = true

  // this is fixed
  private val z3cfg = new Z3Config(
    "MODEL" -> true,
    "MBQI" -> false,
    "SOFT_TIMEOUT" -> 100,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
    )
  toggleWarningMessages(true)

  protected[purescala] var z3: Z3Context = null
  protected[purescala] var program: Program = null
  private var bapa: BAPATheoryType = null
  private var instantiator: AbstractInstantiator = null
  private var neverInitialized = true

  private val IntSetType = SetType(Int32Type)

  override def setProgram(prog: Program): Unit = {
    program = prog
  }

  private def restartZ3: Unit = {
    if (neverInitialized) {
      neverInitialized = false
    } else {
      z3.delete
    }
    z3 = new Z3Context(z3cfg)
    // z3.traceToStdout
    if (useBAPA) bapa = new BAPATheoryType(z3)
    if (useInstantiator) instantiator = new Instantiator(this) else
    if (useFairInstantiator) instantiator = {
      scala.Predef.error("Z3Solver should not be used with FairInst. FairZ3Solver should be used instead.")
    }

    exprToZ3Id = Map.empty
    z3IdToExpr = Map.empty
    counter = 0
    prepareSorts
    prepareFunctions
  }

  private var counter = 0
  private object nextIntForSymbol {
    def apply(): Int = {
      val res = counter
      counter = counter + 1
      res
    }
  }

  private var intSort: Z3Sort = null
  private var boolSort: Z3Sort = null
  private var setSorts: Map[TypeTree, Z3Sort] = Map.empty
  private var intSetMinFun: Z3FuncDecl = null
  private var intSetMaxFun: Z3FuncDecl = null
  private var setCardFuns: Map[TypeTree, Z3FuncDecl] = Map.empty
  private var adtSorts: Map[ClassTypeDef, Z3Sort] = Map.empty
  private var fallbackSorts: Map[TypeTree, Z3Sort] = Map.empty

  protected[purescala] var adtTesters: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  protected[purescala] var adtConstructors: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  protected[purescala] var adtFieldSelectors: Map[Identifier, Z3FuncDecl] = Map.empty

  private var reverseADTTesters: Map[Z3FuncDecl, CaseClassDef] = Map.empty
  private var reverseADTConstructors: Map[Z3FuncDecl, CaseClassDef] = Map.empty
  private var reverseADTFieldSelectors: Map[Z3FuncDecl, (CaseClassDef,Identifier)] = Map.empty

  case class UntranslatableTypeException(msg: String) extends Exception(msg)
  private def prepareSorts: Unit = {
    import Z3Context.{ADTSortReference, RecursiveType, RegularSort}
    // NOTE THAT abstract classes that extend abstract classes are not
    // currently supported in the translation
    intSort = z3.mkIntSort
    boolSort = z3.mkBoolSort
    setSorts = Map.empty
    setCardFuns = Map.empty

    val intSetSort = typeToSort(SetType(Int32Type))
    intSetMinFun = z3.mkFreshFuncDecl("setMin", Seq(intSetSort), intSort)
    intSetMaxFun = z3.mkFreshFuncDecl("setMax", Seq(intSetSort), intSort)

    val roots = program.classHierarchyRoots
    val indexMap: Map[ClassTypeDef, Int] = Map(roots.zipWithIndex: _*)
    //println("indexMap: " + indexMap)

    def typeToSortRef(tt: TypeTree): ADTSortReference = tt match {
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


  def isKnownDef(funDef: FunDef) : Boolean = if(useAnyInstantiator) {
    instantiator.isKnownDef(funDef)
  } else {
    functionMap.isDefinedAt(funDef)
  }
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = {
    if(useAnyInstantiator) {
      instantiator.functionDefToDecl(funDef)
    } else {
      functionMap.getOrElse(funDef, scala.Predef.error("No Z3 definition found for function symbol " + funDef.id.name + ". (Instantiator is off)."))
    }
  }
  def isKnownDecl(decl: Z3FuncDecl) : Boolean = if(useAnyInstantiator) {
    instantiator.isKnownDecl(decl)
  } else {
    reverseFunctionMap.isDefinedAt(decl)
  }
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef = {
    if(useAnyInstantiator) {
      instantiator.functionDeclToDef(decl)
    } else {
      reverseFunctionMap.getOrElse(decl, scala.Predef.error("No FunDef corresponds to Z3 definition " + decl + ". (Instantiator is off)."))
    }
  }
  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty

  def prepareFunctions: Unit = {
    for (funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      if(useAnyInstantiator) {
        instantiator.registerFunction(funDef, sortSeq, returnSort)
      } else {
        val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
        functionMap = functionMap + (funDef -> z3Decl)
        reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
      }
    }

    // Attempts to universally quantify all functions !
    if (!Settings.noForallAxioms && !Settings.useAnyInstantiator) {
      for (funDef <- program.definedFunctions) if (funDef.hasImplementation /* && program.isRecursive(funDef) */ && funDef.args.size > 0) {
        // println("Generating forall axioms for " + funDef.id.name)
        funDef.body.get match {
          case SimplePatternMatching(scrutinee, _, infos) if (
                  funDef.args.size >= 1 && funDef.args.map(_.toVariable).contains(scrutinee)
                  ) => {
            infos.foreach(i => if (!contains(i._4, _.isInstanceOf[MatchExpr])) {
              val argsAsVars: Seq[Option[Variable]] = funDef.args.map(a => {
                val v = a.toVariable
                if (v == scrutinee)
                  None
                else
                  Some(v)
              })
              val otherFunIDs: Seq[Option[Identifier]] = argsAsVars.map(_.map(_.id))
              val otherFunSorts: Seq[Option[Z3Sort]] = argsAsVars.map(_.map(v => typeToSort(v.getType)))
              var c = -1
              val otherFunBounds: Seq[Option[Z3AST]] = for (os <- otherFunSorts) yield {
                os match {
                  case None => None
                  case Some(s) => {
                    c = c + 1
                    Some(z3.mkBound(c, s))
                  }
                }
              }
              val (ccd, pid, subids, dirtyRHS) = i
              val cleanRHS = matchToIfThenElse(dirtyRHS)
              val argSorts: Seq[Z3Sort] = subids.map(id => typeToSort(id.getType))
              val boundVars = argSorts.zip((c + 1) until (c + 1 + argSorts.size)).map(p => z3.mkBound(p._2, p._1))
              val matcher: Z3AST = adtConstructors(ccd)(boundVars: _*)
              val pattern: Z3Pattern = z3.mkPattern(functionDefToDecl(funDef)(
                otherFunBounds.map(_ match {
                  case None => matcher
                  case Some(b) => b
                }): _*))

              val fOfT: Expr = FunctionInvocation(funDef,
                argsAsVars.map(_ match {
                  case None => CaseClass(ccd, subids.map(Variable(_)))
                  case Some(v) => v
                }))

              val toConvert = Equals(fOfT, cleanRHS)
              //println(toConvert)
              val initialMap: Map[Identifier,Z3AST] =
                Map((funDef.args.map(_.id) zip otherFunBounds).map(_ match {
                  case (i, Some(b)) => (i -> b)
                  case (i, None) => (i -> matcher)
                }): _*) ++
                  Map((subids zip boundVars): _*) + (pid -> matcher)

              toZ3Formula(z3, toConvert, initialMap) match {
                case Some(axiomTree) => {
                  val toAssert = if (boundVars.size == 0 && otherFunBounds.flatten.size == 0) {
                    axiomTree
                  } else {
                    val nameTypePairs = (otherFunSorts.flatten ++ argSorts).map(s => (z3.mkIntSymbol(nextIntForSymbol()), s))
                    z3.mkForAll(0, List(pattern), nameTypePairs, axiomTree)
                  }
                  //println("Cool axiom: " + toAssert)
                  z3.assertCnstr(toAssert)
                }
                case None => {
                  reporter.warning("Could not convert to axiom:")
                  reporter.warning(toConvert)
                }
              }
            })
          }
          case _ => {
            // we don't generate axioms that are not simple.
          }
        }
      }
    }
  }

  // assumes prepareSorts has been called....
  def typeToSort(tt: TypeTree): Z3Sort = tt match {
    case Int32Type => intSort
    case BooleanType => boolSort
    case AbstractClassType(cd) => adtSorts(cd)
    case CaseClassType(cd) => {
      if (cd.hasParent) {
        adtSorts(cd.parent.get)
      } else {
        adtSorts(cd)
      }
    }
    case IntSetType if (useBAPA) => bapa.mkSetSort
    case SetType(base) => setSorts.get(base) match {
      case Some(s) => s
      case None => {
        val newSetSort = z3.mkSetSort(typeToSort(base))
        setSorts = setSorts + (base -> newSetSort)
        val newCardFun = z3.mkFreshFuncDecl("card", Seq(newSetSort), z3.mkIntSort)
        setCardFuns = setCardFuns + (base -> newCardFun)
        newSetSort
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

  private var abstractedFormula = false

  override def isUnsat(vc: Expr) = decide(vc, false)

  def solve(vc: Expr) = decide(vc, true)

  def decide(vc: Expr, fv: Boolean) : Option[Boolean] = if(Settings.useAnyInstantiator) {
    decideIterative(vc, fv)
  } else {
    decideStandard(vc, fv)
  }

  def decideStandard(vc: Expr, forValidity: Boolean): Option[Boolean] = {
    restartZ3
    abstractedFormula = false

    lazy val varsInVC = variablesOf(vc) 

    if (neverInitialized) {
      reporter.error("Z3 Solver was not initialized with a PureScala Program.")
      None
    }
    val toConvert = if (forValidity) negate(vc) else vc
    val result = toZ3Formula(z3, toConvert) match {
      case None => None // means it could not be translated
      case Some(z3f) => {
        //z3.push
        z3.assertCnstr(z3f)
        //z3.print
        val actualResult = (z3.checkAndGetModel() match {
          case (Some(true), m) => {
            if (!abstractedFormula) {
              reporter.error("There's a bug!")
              if(Settings.experimental) {
                reporter.error(m)
                printExtractedModel(m, varsInVC)
                if(useBAPA) {
                  reporter.error(bapa.toBapaModel(m))
                }
              }
              Some(false)
            } else {
              reporter.info("Could or could not be a bug (formula was relaxed).")
              if(Settings.experimental) {
                reporter.info(m)
                printExtractedModel(m, varsInVC)
                if(useBAPA) {
                  reporter.error(bapa.toBapaModel(m))
                }
              }
              if(reportUnknownAsSat) {
                Some(false)
              } else {
                None
              }
            }
          }
          case (Some(false), _) => Some(true)
          case (None, m) => {
            reporter.warning("Z3 doesn't know because: " + z3.getSearchFailure.message)
            if(Settings.experimental) {
              reporter.info(m)
            } else {
              if (useBAPA) reporter.error(bapa.toBapaModel(m))
            }
            if(reportUnknownAsSat) {
              Some(false)
            } else {
              None
            }
          }
        })
        //z3.pop(1) 
        actualResult
      }
    }
    result
  }

  def decideIterative(vc: Expr, forValidity: Boolean) : Option[Boolean] = {
    restartZ3
    decideIterativeWithModel(vc, forValidity)._1
  }

  def solveWithBounds(vc: Expr, fv: Boolean) : (Option[Boolean], Map[Identifier,Expr]) = decideIterativeWithBounds(vc, fv)

  def decideIterativeWithBounds(vc: Expr, forValidity: Boolean) : (Option[Boolean], Map[Identifier, Expr]) = {
    restartZ3
    boundValues
    decideIterativeWithModel(vc, forValidity)
  }

  def decideIterativeWithModel(vc: Expr, forValidity: Boolean) : (Option[Boolean], Map[Identifier, Expr]) = {
    assert(instantiator != null)
    assert(!useBAPA)

    lazy val varsInVC = variablesOf(vc) 

    if (neverInitialized) {
      reporter.error("Z3 Solver was not initialized with a PureScala Program.")
      None
    }
    val toConvert = if (forValidity) negate(vc) else vc
    val toCheckAgainstModels = toConvert

    val result : (Option[Boolean], Map[Identifier, Expr]) = toZ3Formula(z3, toConvert) match {
      case None => (None, Map.empty) // means it could not be translated
      case Some(z3f) => {
        z3.assertCnstr(z3f)

        // THE LOOP STARTS HERE.
        var foundDefinitiveSolution : Boolean = false
        var finalResult : (Option[Boolean], Map[Identifier, Expr]) = (None, Map.empty)

        while(!foundDefinitiveSolution && instantiator.possibleContinuation) {
          instantiator.increaseSearchDepth()
          z3.checkAndGetModel() match {
            case (Some(false), _) => {
              // This means a definitive proof of unsatisfiability has been found.
              foundDefinitiveSolution = true
              finalResult = (Some(true), Map.empty)
            }

            case (outcome, m) if (reportUnknownAsSat || outcome == Some(true)) => {
              import Evaluator._

              // WE HAVE TO CHECK THE COUNTER-EXAMPLE.
              val asMap = modelToMap(m, varsInVC)
              lazy val modelAsString = asMap.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
              reporter.info("  - A candidate counter-example was found... Examining...")
              //reporter.info(modelAsString)


              //println("(I'm going to pretend this never happened...)")

              val evalResult = eval(asMap, toCheckAgainstModels)

              
              evalResult match {
                case OK(BooleanLiteral(true)) => {
                  reporter.error("Counter-example found and confirmed:")
                  reporter.error(modelAsString)
                  foundDefinitiveSolution = true
                  finalResult = (Some(false), asMap)
                }
                case InfiniteComputation() => {
                  reporter.info("Model seems to lead to divergent computation.")
                  reporter.error(modelAsString)
                  foundDefinitiveSolution = true
                  finalResult = (None, asMap)
                }
                case RuntimeError(msg) => {
                  reporter.info("Model leads to runtime error: " + msg)
                  reporter.error(modelAsString)
                  foundDefinitiveSolution = true
                  finalResult = (Some(false), asMap)
                }
                case t @ TypeError(_,_) => {
                  scala.Predef.error("Type error in model evaluation.\n" + t.msg)
                }
                case _ => {
                  reporter.info("    -> candidate model discarded.")
                }
              }
            
              m.delete
            }

            case (None, m) => {
              reporter.warning("Iterative Z3 gave up because: " + z3.getSearchFailure.message)
              foundDefinitiveSolution = true
              finalResult = (None, modelToMap(m, varsInVC))
              m.delete
            }
          }
        }
        finalResult
      }
    }
    result
  }

  protected[purescala] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[purescala] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty
  protected[purescala] def toZ3Formula(z3: Z3Context, expr: Expr, initialMap: Map[Identifier,Z3AST] = Map.empty): Option[Z3AST] = {
    class CantTranslateException extends Exception

    val varsInformula: Set[Identifier] = variablesOf(expr)

    var z3Vars: Map[Identifier,Z3AST] = if(!initialMap.isEmpty) {
      initialMap
    } else {
      // FIXME TODO pleeeeeeeease make this cleaner. Ie. decide what set of
      // variable has to remain in a map etc.
      exprToZ3Id.filter(p => p._1.isInstanceOf[Variable]).map(p => (p._1.asInstanceOf[Variable].id -> p._2))
    }
    // exprToZ3Id = Map.empty
    // z3IdToExpr = Map.empty

    for((k, v) <- initialMap) {
      exprToZ3Id += (k.toVariable -> v)
      z3IdToExpr += (v -> k.toVariable)
    }

    def rec(ex: Expr): Z3AST = { 
      //println("Stacking up call for:")
      //println(ex)
      val recResult = (ex match {
      case Let(i, e, b) => {
        val re = rec(e)
        z3Vars = z3Vars + (i -> re)
        val rb = rec(b)
        z3Vars = z3Vars - i
        rb
      }
      case e @ Error(_) => {
        val tpe = e.getType
        val newAST = z3.mkFreshConst("errorValue", typeToSort(tpe))
        exprToZ3Id += (e -> newAST)
        z3IdToExpr += (newAST -> e)
        newAST
      }
      case v@Variable(id) => z3Vars.get(id) match {
        case Some(ast) => ast
        case None => {
          if (id.isLetBinder) {
            //scala.Predef.error("Error in formula being translated to Z3: identifier " + id + " seems to have escaped its let-definition")
          }
          val newAST = z3.mkFreshConst(id.name, typeToSort(v.getType))
          z3Vars = z3Vars + (id -> newAST)
          exprToZ3Id += (v -> newAST)
          z3IdToExpr += (newAST -> v)
          newAST
        }
      }
      case IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec(_)): _*)
      case Or(exs) => z3.mkOr(exs.map(rec(_)): _*)
      case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
      case Iff(l, r) => {
        val rl = rec(l)
        val rr = rec(r)
        z3.mkAnd(z3.mkImplies(rl, rr), z3.mkImplies(rr, rl))
      }
      case Not(Iff(l, r)) => z3.mkXor(rec(l), rec(r))
      case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case IntLiteral(v) => z3.mkInt(v, intSort)
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l, r) => z3.mkEq(rec(l), rec(r))
      case Plus(l, r) => z3.mkAdd(rec(l), rec(r))
      case Minus(l, r) => z3.mkSub(rec(l), rec(r))
      case Times(l, r) => z3.mkMul(rec(l), rec(r))
      case Division(l, r) => z3.mkDiv(rec(l), rec(r))
      case UMinus(e) => z3.mkUnaryMinus(rec(e))
      case LessThan(l, r) => z3.mkLT(rec(l), rec(r))
      case LessEquals(l, r) => z3.mkLE(rec(l), rec(r))
      case GreaterThan(l, r) => z3.mkGT(rec(l), rec(r))
      case GreaterEquals(l, r) => z3.mkGE(rec(l), rec(r))
      case c@CaseClass(cd, args) => {
        val constructor = adtConstructors(cd)
        constructor(args.map(rec(_)): _*)
      }
      case c@CaseClassSelector(_, cc, sel) => {
        val selector = adtFieldSelectors(sel)
        selector(rec(cc))
      }
      case c@CaseClassInstanceOf(ccd, e) => {
        val tester = adtTesters(ccd)
        tester(rec(e))
      }
      case f@FunctionInvocation(fd, args) => {
        z3.mkApp(functionDefToDecl(fd), args.map(rec(_)): _*)
      }
      case e@EmptySet(_) => if (useBAPA && e.getType == IntSetType) {
        bapa.mkEmptySet
      } else {
        z3.mkEmptySet(typeToSort(e.getType.asInstanceOf[SetType].base))
      }
      case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
      case ElementOfSet(e, s) => if (useBAPA && s.getType == IntSetType) {
        bapa.mkElementOf(rec(e), rec(s))
      } else {
        z3.mkSetSubset(z3.mkSetAdd(z3.mkEmptySet(typeToSort(e.getType)), rec(e)), rec(s))
      }
      case SubsetOf(s1, s2) => if (useBAPA && s1.getType == IntSetType) {
        bapa.mkSubsetEq(rec(s1), rec(s2))
      } else {
        z3.mkSetSubset(rec(s1), rec(s2))
      }
      case SetIntersection(s1, s2) => if (useBAPA && s1.getType == IntSetType) {
        bapa.mkIntersect(rec(s1), rec(s2))
      } else {
        z3.mkSetIntersect(rec(s1), rec(s2))
      }
      case SetUnion(s1, s2) => if (useBAPA && s1.getType == IntSetType) {
        bapa.mkUnion(rec(s1), rec(s2))
      } else {
        z3.mkSetUnion(rec(s1), rec(s2))
      }
      case SetDifference(s1, s2) => if (useBAPA && s1.getType == IntSetType) {
        bapa.mkIntersect(rec(s1), bapa.mkComplement(rec(s2)))
      } else {
        z3.mkSetDifference(rec(s1), rec(s2))
      }
      case f@FiniteSet(elems) => if (useBAPA && f.getType == IntSetType) {
        elems.map(e => bapa.mkSingleton(rec(e))).reduceLeft(bapa.mkUnion(_, _))
      } else {
        elems.foldLeft(z3.mkEmptySet(typeToSort(f.getType.asInstanceOf[SetType].base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))
      }
      case SetCardinality(s) => if (useBAPA && s.getType == IntSetType) {
        bapa.mkCard(rec(s))
      } else {
        val rs = rec(s)
        setCardFuns(s.getType.asInstanceOf[SetType].base)(rs)
      }
      case SetMin(s) => intSetMinFun(rec(s))
      case SetMax(s) => intSetMaxFun(rec(s))

      case _ => {
        reporter.warning("Can't handle this in translation to Z3: " + ex)
        throw new CantTranslateException
      }
    })
    // println("Encoding of:")
    // println(ex)
    // println("...was encoded as:")
    // println(recResult)
    recResult
    }

    try {
      val res = Some(rec(expr))
      // val usedInZ3Form = z3Vars.keys.toSet
      // println("Variables in formula:   " + varsInformula.map(_.uniqueName))
      // println("Variables passed to Z3: " + usedInZ3Form.map(_.uniqueName))
      res
    } catch {
      case e: CantTranslateException => None
    }
  }

  protected[purescala] def fromZ3Formula(tree : Z3AST) : Expr = {
    def rec(t: Z3AST) : Expr = z3.getASTKind(t) match {
      case Z3AppAST(decl, args) => {
        val argsSize = args.size
        if(argsSize == 0 && z3IdToExpr.isDefinedAt(t)) {
          val toRet = z3IdToExpr(t)
          // println("Map says I should replace " + t + " by " + toRet)
          toRet
        } else if(isKnownDecl(decl)) {
          val fd = functionDeclToDef(decl)
          assert(fd.args.size == argsSize)
          FunctionInvocation(fd, args.map(rec(_)))
        } else if(argsSize == 1 && reverseADTTesters.isDefinedAt(decl)) {
          CaseClassInstanceOf(reverseADTTesters(decl), rec(args(0)))
        } else if(argsSize == 1 && reverseADTFieldSelectors.isDefinedAt(decl)) {
          val (ccd, fid) = reverseADTFieldSelectors(decl)
          CaseClassSelector(ccd, rec(args(0)), fid)
        } else if(reverseADTConstructors.isDefinedAt(decl)) {
          val ccd = reverseADTConstructors(decl)
          assert(argsSize == ccd.fields.size)
          CaseClass(ccd, args.map(rec(_)))
        } else {
          import Z3DeclKind._
          val rargs = args.map(rec(_))
          z3.getDeclKind(decl) match {
            case OpTrue => BooleanLiteral(true)
            case OpFalse => BooleanLiteral(false)
            case OpEq => Equals(rargs(0), rargs(1))
            case OpITE => {
              assert(argsSize == 3)
              val r0 = rargs(0)
              val r1 = rargs(1)
              val r2 = rargs(2)
              try {
                IfExpr(r0, r1, r2).setType(leastUpperBound(r1.getType, r2.getType))
              } catch {
                case e => {
                  println("I was asking for lub because of this.")
                  println(t)
                  println("which was translated as")
                  println(IfExpr(r0,r1,r2))
                  throw e
                }
              }
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
            case other => {
              System.err.println("Don't know what to do with this declKind : " + other)
              throw new CantTranslateException(t)
            }
          }
        }
      }

      case Z3NumeralAST(Some(v)) => IntLiteral(v)
      case other @ _ => {
        System.err.println("Don't know what this is " + other) 
        if(useAnyInstantiator) {
          instantiator.dumpFunctionMap
        } else {
          System.err.println("REVERSE FUNCTION MAP:")
          System.err.println(reverseFunctionMap.toSeq.mkString("\n"))
        }
        System.err.println("REVERSE CONS MAP:")
        System.err.println(reverseADTConstructors.toSeq.mkString("\n"))
        // System.exit(-1)
        throw new CantTranslateException(t)
      }
    }

    rec(tree)
  }
}
