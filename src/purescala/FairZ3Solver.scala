package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

class FairZ3Solver(val reporter: Reporter) extends Solver(reporter) with AbstractZ3Solver with Z3ModelReconstruction {
  // have to comment this to use the solver for constraint solving...
  // assert(Settings.useFairInstantiator)

  private final val UNKNOWNASSAT : Boolean = false

  val description = "Fair Z3 Solver"
  override val shortDescription = "Z3-f"

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
  private var neverInitialized = true

  private var unrollingBank: UnrollingBank = null
  private var blockingSet: Set[Expr] = Set.empty
  private var toCheckAgainstModels: Expr = BooleanLiteral(true)
  private var varsInVC: Set[Identifier] = Set.empty

  override def setProgram(prog: Program): Unit = {
    program = prog
  }

  def restartZ3: Unit = {
    if (neverInitialized) {
      neverInitialized = false
    } else {
      z3.delete
    }
    z3 = new Z3Context(z3cfg)
    //z3.traceToStdout

    exprToZ3Id = Map.empty
    z3IdToExpr = Map.empty
    counter = 0
    prepareSorts
    prepareFunctions

    unrollingBank = new UnrollingBank
    blockingSet = Set.empty
    toCheckAgainstModels = BooleanLiteral(true)
    varsInVC = Set.empty
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

  def isKnownDef(funDef: FunDef) : Boolean = functionMap.isDefinedAt(funDef)
  
  def functionDefToDecl(funDef: FunDef) : Z3FuncDecl = 
      functionMap.getOrElse(funDef, scala.Predef.error("No Z3 definition found for function symbol " + funDef.id.name + "."))

  def isKnownDecl(decl: Z3FuncDecl) : Boolean = reverseFunctionMap.isDefinedAt(decl)
  
  def functionDeclToDef(decl: Z3FuncDecl) : FunDef = 
      reverseFunctionMap.getOrElse(decl, scala.Predef.error("No FunDef corresponds to Z3 definition " + decl + "."))

  private var functionMap: Map[FunDef, Z3FuncDecl] = Map.empty
  private var reverseFunctionMap: Map[Z3FuncDecl, FunDef] = Map.empty

  def prepareFunctions: Unit = {
    functionMap = Map.empty
    reverseFunctionMap = Map.empty
    for (funDef <- program.definedFunctions) {
      val sortSeq = funDef.args.map(vd => typeToSort(vd.tpe))
      val returnSort = typeToSort(funDef.returnType)

      val z3Decl = z3.mkFreshFuncDecl(funDef.id.name, sortSeq, returnSort)
      functionMap = functionMap + (funDef -> z3Decl)
      reverseFunctionMap = reverseFunctionMap + (z3Decl -> funDef)
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

  override def isUnsat(vc: Expr) = decide(vc, false)

  def solve(vc: Expr) = decide(vc, true)

  def solveWithBounds(vc: Expr, fv: Boolean) : (Option[Boolean], Map[Identifier,Expr]) = {
    restartZ3
    boundValues
    decideWithModel(vc, fv)
  }

  def decide(vc: Expr, forValidity: Boolean):Option[Boolean] = {
    restartZ3
    decideWithModel(vc, forValidity)._1
  }

  def restartAndDecideWithModel(vc: Expr, forValidity: Boolean): (Option[Boolean], Map[Identifier,Expr]) = {
    restartZ3
    decideWithModel(vc, forValidity)
  }

  def decideWithModel(vc: Expr, forValidity: Boolean): (Option[Boolean], Map[Identifier,Expr]) = {
    var forceStop : Boolean = false

    var foundDefinitiveAnswer : Boolean = false
    def stopCallback() : Unit = {
      if(!foundDefinitiveAnswer) {
        reporter.error(" - Timeout reached.")
        forceStop = true
        z3.softCheckCancel
      }
    }

    val timer : Option[Timer] = Settings.solverTimeout.map(t => new Timer(stopCallback, t))
    timer.foreach(_.start())

    var definitiveAnswer : Option[Boolean] = None
    var definitiveModel : Map[Identifier,Expr] = Map.empty
    def foundAnswer(answer : Option[Boolean], model : Map[Identifier,Expr] = Map.empty) : Unit = {
      foundDefinitiveAnswer = true
      definitiveAnswer = answer
      definitiveModel = model
      timer.foreach(t => t.halt)
    }

    if (neverInitialized) {
      reporter.error("Z3 Solver was not initialized with a PureScala Program.")
      None
    }

    val expandedVC = expandLets(if (forValidity) negate(vc) else vc)
    toCheckAgainstModels = And(toCheckAgainstModels,expandedVC)

    varsInVC ++= variablesOf(expandedVC)

    reporter.info(" - Initial unrolling...")
    val (basis, clauses, guards) = unrollingBank.closeUnrollings(expandedVC)
    // println("Here is what we want to check against models : " + toCheckAgainstModels)
    // println("New basis: " + e)
    // println("Bunch of clauses:\n" + se.map(_.toString).mkString("\n"))
    // println("Bunch of blocking bools: " + sib.map(_.toString).mkString(", "))

    // println("Basis : " + basis)
    z3.assertCnstr(toZ3Formula(z3, basis).get)
    // println(toZ3Formula(z3, basis).get)
    // for(clause <- clauses) {
    //   println("we're getting a new clause " + clause)
    //   z3.assertCnstr(toZ3Formula(z3, clause).get)
    // }
    z3.assertCnstr(toZ3Formula(z3, And(clauses)).get)

    blockingSet ++= Set(guards.map(p => if(p._2) Not(Variable(p._1)) else Variable(p._1)) : _*)

    var iterationsLeft : Int = if(Settings.unrollingLevel > 0) Settings.unrollingLevel else 16121984

    while(!foundDefinitiveAnswer && !forceStop) {
      iterationsLeft -= 1

      val blockingSetAsZ3 : Seq[Z3AST] = blockingSet.map(toZ3Formula(z3, _).get).toSeq
      // println("Blocking set : " + blockingSet)

      if(Settings.useCores) {
        // NOOP
      } else {
        z3.push
        if(!blockingSetAsZ3.isEmpty)
          z3.assertCnstr(z3.mkAnd(blockingSetAsZ3 : _*))
      }

      reporter.info(" - Running Z3 search...")
      val (answer, model, core) : (Option[Boolean], Z3Model, Seq[Z3AST]) = if(Settings.useCores) {
        println(blockingSetAsZ3)
        z3.checkAssumptions(blockingSetAsZ3 : _*)
      } else {
        val (a, m) = z3.checkAndGetModel()
        (a, m, Seq.empty[Z3AST])
      }

      val reinterpretedAnswer = if(!UNKNOWNASSAT) answer else (answer match {
        case None | Some(true) => Some(true)
        case Some(false) => Some(false)
      })

      (reinterpretedAnswer, model) match {
        case (None, m) => { // UNKNOWN
          reporter.warning("Z3 doesn't know because: " + z3.getSearchFailure.message)
          foundAnswer(None)
          m.delete

          if(!Settings.useCores) {
            z3.pop(1)
          }
        }
        case (Some(true), m) => { // SAT
          val (trueModel, model) = validateAndDeleteModel(m, toCheckAgainstModels, varsInVC)

          if (trueModel) {
            foundAnswer(Some(false), model)
          } else {
            reporter.error("Something went wrong. The model should have been valid, yet we got this : ")
            reporter.error(model)
            foundAnswer(None, model)
          }

          if(!Settings.useCores) {
            z3.pop(1)
          }
        }
        case (Some(false), m) if Settings.useCores && core.isEmpty => {
          reporter.info("Empty core, definitively valid.")
          m.delete
          foundAnswer(Some(true))
        }
        case (Some(false), m) if !Settings.useCores && blockingSet.isEmpty => {
          foundAnswer(Some(true))
          z3.pop(1)
        }
        // This branch is both for with and without unsat cores. The
        // distinction is made inside.
        case (Some(false), m) => {
          //m.delete

          if(!Settings.useCores) {
            z3.pop(1)
            
            val (result2,m2) = z3.checkAndGetModel()

            if (result2 == Some(false)) {
              foundAnswer(Some(true))
            } else {
              // we might have been lucky :D
              val (wereWeLucky, cleanModel) = validateAndDeleteModel(m2, toCheckAgainstModels, varsInVC)
              if(wereWeLucky) {
                foundAnswer(Some(false), cleanModel)
              } 
            }
          }

          if(forceStop) {
            foundAnswer(None)
          }
            
          if(!foundDefinitiveAnswer) { 
            reporter.info("- We need to keep going.")

            val toRelease : Set[Expr] = if(Settings.useCores) {
              core.map(ast => fromZ3Formula(ast) match {
                case n @ Not(Variable(_)) => n
                case v @ Variable(_) => v
                case _ => scala.Predef.error("Impossible element extracted from core: " + ast)
              }).toSet
            } else {
              blockingSet
            }

            var fixedForEver : Set[Expr] = Set.empty

            if(Settings.pruneBranches) {
              for(ex <- blockingSet) ex match {
                case Not(Variable(b)) => {
                  z3.push
                  z3.assertCnstr(toZ3Formula(z3, Variable(b)).get)
                  z3.check match {
                    case Some(false) => {
                      //println("We had ~" + b + " in the blocking set. We now know it should stay there forever.")
                      z3.pop(1)
                      z3.assertCnstr(toZ3Formula(z3, Not(Variable(b))).get)
                      fixedForEver = fixedForEver + ex
                    }
                    case _ => z3.pop(1)
                  }
                }
                case Variable(b) => {
                  z3.push
                  z3.assertCnstr(toZ3Formula(z3, Not(Variable(b))).get)
                  z3.check match {
                    case Some(false) => {
                      //println("We had " + b + " in the blocking set. We now know it should stay there forever.")
                      z3.pop(1)
                      z3.assertCnstr(toZ3Formula(z3, Variable(b)).get)
                      fixedForEver = fixedForEver + ex
                    }
                    case _ => z3.pop(1)
                  }
                }
                case _ => scala.Predef.error("Should not have happened.")
              }
              if(fixedForEver.size > 0) {
                reporter.info("- Pruned out " + fixedForEver.size + " branches.")
              }
            }

            // println("Release set : " + toRelease)

            blockingSet = blockingSet -- toRelease

            val toReleaseAsPairs : Set[(Identifier,Boolean)] = (toRelease -- fixedForEver).map(b => b match {
              case Variable(id) => (id, true)
              case Not(Variable(id)) => (id, false)
              case _ => scala.Predef.error("Impossible value in release set: " + b)
            })

            reporter.info(" - more unrollings")
            for((id,polarity) <- toReleaseAsPairs) {
              val (newClauses,newBlockers) = unrollingBank.unlock(id, !polarity)
              // for(clause <- newClauses) {
              //   println("we're getting a new clause " + clause)
              //   z3.assertCnstr(toZ3Formula(z3, clause).get)
              // }

              for(ncl <- newClauses) {
                z3.assertCnstr(toZ3Formula(z3, ncl).get)
              }
              //z3.assertCnstr(toZ3Formula(z3, And(newClauses)).get)
              blockingSet = blockingSet ++ Set(newBlockers.map(p => if(p._2) Not(Variable(p._1)) else Variable(p._1)) : _*)
            }
          }
        }
      }

      if(iterationsLeft <= 0) {
        reporter.error(" - Max. number of iterations reached.")
        foundAnswer(None)
      }
    }

    if(forceStop) {
      (None, Map.empty)
    } else {
      assert(foundDefinitiveAnswer)
      (definitiveAnswer, definitiveModel)
    }
  }

  private def validateAndDeleteModel(model: Z3Model, formula: Expr, variables: Set[Identifier]) : (Boolean, Map[Identifier,Expr]) = {
    import Evaluator._

    val asMap = modelToMap(model, variables)
    model.delete

    lazy val modelAsString = asMap.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
    val evalResult = eval(asMap, formula)

    evalResult match {
      case OK(BooleanLiteral(true)) => {
        reporter.info("- Model validated:")
        reporter.info(modelAsString)
        (true, asMap)
      }
      case RuntimeError(msg) => {
        reporter.info("- Model leads to runtime error: " + msg)
        reporter.error(modelAsString)
        (true, asMap)
      }
      case OK(BooleanLiteral(false)) => {
        reporter.info("- Invalid model.")
        (false, Map.empty)
      }
      case other => {
        reporter.error("Something went wrong. While evaluating the model, we got this: " + other)
        (false, Map.empty)
      }
    }
  }


  // the last return value is a map binding ite values to boolean switches
  private def clausifyITE(formula : Expr) : (Expr, List[Expr], Map[Identifier,Identifier]) = {
    var newClauses : List[Expr] = Nil
    var ite2Bools : Map[Identifier,Identifier] = Map.empty

    def clausify(ex : Expr) : Option[Expr] = ex match {
      case ie @ IfExpr(cond, then, elze) => {
        val switch = FreshIdentifier("path", true).setType(BooleanType).toVariable
        val placeHolder = FreshIdentifier("iteval", true).setType(ie.getType).toVariable
        newClauses = Iff(switch, cond) :: newClauses
        newClauses = Implies(switch, Equals(placeHolder, then)) :: newClauses
        newClauses = Implies(Not(switch), Equals(placeHolder, elze)) :: newClauses
        // newBools = newBools + switch.id
        ite2Bools = ite2Bools + (placeHolder.id -> switch.id)
        Some(placeHolder)
      }
      case _ => None
    }

    val cleanedUp = searchAndReplaceDFS(clausify)(formula)

    (cleanedUp, newClauses.reverse, ite2Bools)
  }

  protected[purescala] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[purescala] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty
  protected[purescala] def toZ3Formula(z3: Z3Context, expr: Expr, initialMap: Map[Identifier,Z3AST] = Map.empty) : Option[Z3AST] = {
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
              scala.Predef.error("Error in formula being translated to Z3: identifier " + id + " seems to have escaped its let-definition")
            }
            val newAST = z3.mkFreshConst(id.uniqueName/*name*/, typeToSort(v.getType))
            z3Vars = z3Vars + (id -> newAST)
            exprToZ3Id += (v -> newAST)
            z3IdToExpr += (newAST -> v)
            newAST
          }
        }
        // case ite @ IfExpr(c, t, e) => {
        //   val switch = z3.mkFreshConst("path", z3.mkBoolSort)
        //   val placeHolder = z3.mkFreshConst("ite", typeToSort(ite.getType))
        //   val clause1 = z3.mkIff(switch, rec(c))
        //   val clause2 = z3.mkImplies(switch, z3.mkEq(placeHolder, rec(t)))
        //   val clause3 = z3.mkImplies(z3.mkNot(switch), z3.mkEq(placeHolder, rec(e)))

        //   accumulatedClauses = clause3 :: clause2 :: clause1 :: accumulatedClauses

        //   placeHolder
        // }
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
        case e@EmptySet(_) => z3.mkEmptySet(typeToSort(e.getType.asInstanceOf[SetType].base))
        
        case SetEquals(s1, s2) => z3.mkEq(rec(s1), rec(s2))
        case ElementOfSet(e, s) => z3.mkSetSubset(z3.mkSetAdd(z3.mkEmptySet(typeToSort(e.getType)), rec(e)), rec(s))
        case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
        case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))
        case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
        case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
        case f@FiniteSet(elems) => elems.foldLeft(z3.mkEmptySet(typeToSort(f.getType.asInstanceOf[SetType].base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))
        case SetCardinality(s) => {
          val rs = rec(s)
          setCardFuns(s.getType.asInstanceOf[SetType].base)(rs)
        }
        case SetMin(s) => intSetMinFun(rec(s))
        case SetMax(s) => intSetMaxFun(rec(s))
        
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
        System.err.println("REVERSE FUNCTION MAP:")
        System.err.println(reverseFunctionMap.toSeq.mkString("\n"))
        System.err.println("REVERSE CONS MAP:")
        System.err.println(reverseADTConstructors.toSeq.mkString("\n"))
        throw new CantTranslateException(t)
      }
    }

    rec(tree)
  }

  // This remembers everything that was unrolled, which literal is blocking
  // which calls, etc.
  class UnrollingBank {
    private val everythingEverUnrolled : MutableSet[FunctionInvocation] = MutableSet.empty

    // stores the invocations that boolean literals are guarding.
    private val blocked : MutableMap[(Identifier,Boolean),Set[FunctionInvocation]] = MutableMap.empty

    def wasUnrolledBefore(functionInvocation : FunctionInvocation) : Boolean = {
      everythingEverUnrolled(functionInvocation)
    }

    private def registerAsUnrolled(functionInvocation : FunctionInvocation) : Unit = {
      everythingEverUnrolled += functionInvocation
    }

    def closeUnrollings2(formula : Expr) : (Expr, Seq[Expr], Seq[(Identifier,Boolean)]) = {

      scala.Predef.error("wtf")
    }

    def closeUnrollings(formula : Expr) : (Expr, Seq[Expr], Seq[(Identifier,Boolean)]) = {
      var (basis, clauses, ite2Bools) = clausifyITE(formula)

      var unrolledNow : Set[FunctionInvocation] = Set.empty
      var stillToUnroll : Set[FunctionInvocation] = Set.empty
      var treatedClauses : List[Expr] = Nil
      var blockers : List[(Identifier,Boolean)] = Nil

      stillToUnroll = stillToUnroll ++ topLevelFunctionCallsOf(basis)
      do {
        // We go through each clause and figure out what must be enrolled and
        // what must be blocked. We register everything.
        for(clause <- clauses) {
          clause match {
            case Iff(Variable(_), cond) => {
              stillToUnroll = stillToUnroll ++ topLevelFunctionCallsOf(cond)
            }
            // TODO : sort out the functions that are not recursive and unroll
            // them in any case
            case Implies(v @ Variable(id), then) => {
              val calls = topLevelFunctionCallsOf(then)
              if(!calls.isEmpty) {
                assert(!blocked.isDefinedAt((id,true)))
                blocked((id,true)) = calls
                blockers = (id,true) :: blockers
              }
            }
            case Implies(Not(v @ Variable(id)), elze) => {
              val calls = topLevelFunctionCallsOf(elze)
              if(!calls.isEmpty) {
                assert(!blocked.isDefinedAt((id,false)))
                blocked((id,false)) = calls
                blockers = (id,false) :: blockers
              }
            }
            case _ => scala.Predef.error("Who added this as a clause? " + clause)
          }
          treatedClauses = clause :: treatedClauses
        }

        clauses = Nil

        while(!stillToUnroll.isEmpty) {
          val copy = stillToUnroll
          stillToUnroll = Set.empty

          for(stu <- (copy -- unrolledNow) if !wasUnrolledBefore(stu)) {
            // println("unrolling " + stu)
            val unrolled : Seq[Expr] = unroll(stu) // that's between 0 and two formulas
            registerAsUnrolled(stu)
            unrolledNow = unrolledNow + stu
            
            for(formula <- unrolled) {
              val (basis2, clauses2, _) = clausifyITE(formula)
              stillToUnroll = stillToUnroll ++ topLevelFunctionCallsOf(basis2)
              clauses = clauses2 ::: clauses
              treatedClauses = basis2 :: treatedClauses
            }
          }
        }
        
      } while(!clauses.isEmpty)

      (basis, treatedClauses.reverse, blockers.reverse)
    }

    // takes in a conjunction and returns a new conjunction, where all
    // non-recursive function calls are "defined" and "contracted"
    def expandAllNonRecursive(exprs: List[Expr]) : List[Expr] = {
      val todo : MutableSet[FunctionInvocation] = MutableSet.empty
      val todo2 : MutableSet[FunctionInvocation] = MutableSet.empty
      var resulting : List[Expr] = Nil

      for(expr <- exprs) {
        todo ++= allNonRecursiveFunctionCallsOf(expr, program)
        resulting = expr :: resulting
      }

      while(!todo.isEmpty) {
        todo2.clear
        for(fi <- todo) if(!wasUnrolledBefore(fi)) {
          registerAsUnrolled(fi)
          val ur = unroll(fi)
          resulting = ur ::: resulting
          for(u <- ur) {
            todo2 ++= allNonRecursiveFunctionCallsOf(u, program)
          }
        }
        todo.clear
        todo ++= todo2
      }

      resulting
    }

    // Returns between 0 and 2 tautologies with respect to the interpretation of
    // the function and its postcondition.
    private def unroll(functionInvocation: FunctionInvocation) : List[Expr] = {
      val FunctionInvocation(fd, args) = functionInvocation
      val postExpr = if(fd.hasPostcondition) {
        val post = expandLets(matchToIfThenElse(fd.postcondition.get))
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*) + (ResultVariable() -> functionInvocation)
        val newBody = replace(substMap, post)
        List(newBody)
      } else Nil
    
      val bodyExpr = if(fd.hasBody) {
        val body = expandLets(matchToIfThenElse(fd.body.get))
        val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip args) : _*)
        val newBody = replace(substMap, body)
        List(Equals(functionInvocation, newBody))
      } else Nil

      postExpr ::: bodyExpr
    }

    // if polarity == true, means that we used to have !id in the blocking set,
    // and that now it's gone. As a result, we need to unroll everything that
    // id is guarding. Similarly for polarity == false
    def unlock(id: Identifier, polarity: Boolean) : (Seq[Expr], Seq[(Identifier,Boolean)]) = {
      if(!blocked.isDefinedAt((id,polarity))) {
        (Seq.empty,Seq.empty)
      } else {
        var newBlockers : Set[(Identifier,Boolean)] = Set.empty
        var newClauses : List[Expr] = Nil

        val blockedSet = blocked((id,polarity))

        for(functionInvocation <- blockedSet) {
          // TODO this is probably where the unrolling of the recursive call
          // should actually occur, rather than delegating that to
          // closeUnrollings.
          val (_, clauses, blockers) = closeUnrollings(functionInvocation)
          newClauses = newClauses ++ clauses
          newBlockers = newBlockers ++ blockers
        }

        (newClauses, newBlockers.toSeq)
      }
    }

    private var invocations : List[FunctionInvocation] = Nil

    def addInvocation(blocker: Identifier, polarity: Boolean, invocation: FunctionInvocation) : Unit = {
      invocations = invocation :: invocations
    }


  }
}

