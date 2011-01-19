package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

import scala.collection.mutable.{HashMap => MutableHashMap}

class FairZ3Solver(val reporter: Reporter) extends Solver(reporter) with AbstractZ3Solver with Z3ModelReconstruction {
  assert(Settings.useFairInstantiator)

  val description = "Fair Z3 Solver"
  override val shortDescription = "Z3-f"

  // this is fixed
  private val z3cfg = new Z3Config(
    "MODEL" -> true,
    "SOFT_TIMEOUT" -> 100,
    "TYPE_CHECK" -> true,
    "WELL_SORTED_CHECK" -> true
    )
  toggleWarningMessages(true)

  protected[purescala] var z3: Z3Context = null
  protected[purescala] var program: Program = null
  private var neverInitialized = true

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

  private var adtTesters: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  private var adtConstructors: Map[CaseClassDef, Z3FuncDecl] = Map.empty
  private var adtFieldSelectors: Map[Identifier, Z3FuncDecl] = Map.empty

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

  def decide(vc: Expr, forValidity: Boolean):Option[Boolean] = decideWithModel(vc, forValidity)._1
  def decideWithModel(vc: Expr, forValidity: Boolean): (Option[Boolean], Map[Identifier,Expr]) = {
    restartZ3

    lazy val varsInVC = variablesOf(vc) 

    if (neverInitialized) {
      reporter.error("Z3 Solver was not initialized with a PureScala Program.")
      None
    }
    val toConvert = if (forValidity) negate(vc) else vc
    val toCheckAgainstModels = toConvert

    val result : (Option[Boolean],Map[Identifier,Expr]) = toZ3Formula(z3, toConvert) match {
      case None => (None, Map.empty) // means it could not be translated
      case Some((z3f, clauses)) => {
        z3.assertCnstr(z3f)
        println(z3f)
        for(clause <- clauses) {
          z3.assertCnstr(clause)
          println(clause)
        }

        var foundDefinitiveSolution = false

        val actualResult : (Option[Boolean],Map[Identifier,Expr]) = (z3.checkAndGetModel() match {
          case (Some(true), m) => {
            import Evaluator._

            // WE HAVE TO CHECK THE COUNTER-EXAMPLE.
            val asMap = modelToMap(m, varsInVC)
            lazy val modelAsString = asMap.toList.map(p => p._1 + " -> " + p._2).mkString("\n")
            reporter.info("  - A candidate counter-example was found... Examining...")
            reporter.info(modelAsString)

            val evalResult = eval(asMap, toCheckAgainstModels)
            
            evalResult match {
              case OK(BooleanLiteral(true)) => {
                reporter.error("Counter-example found and confirmed:")
                reporter.error(modelAsString)
                foundDefinitiveSolution = true
                (Some(false), asMap)
              }
              case OK(BooleanLiteral(false)) => {
                reporter.info("Not a valid counter-example. Must.. keep.. going..")
                (None, asMap)
              }
              case InfiniteComputation() => {
                reporter.info("Model seems to lead to divergent computation.")
                reporter.error(modelAsString)
                foundDefinitiveSolution = true
                (None, asMap)
              }
              case RuntimeError(msg) => {
                reporter.info("Model leads to runtime error: " + msg)
                reporter.error(modelAsString)
                foundDefinitiveSolution = true
                (Some(false), asMap)
              }
              case t @ TypeError(_,_) => {
                scala.Predef.error("Type error in model evaluation.\n" + t.msg)
              }
              case _ => {
                scala.Predef.error("Why am I here?")
              }
            }
          }
          case (Some(false), _) => (Some(true), Map.empty)
          case (None, m) => {
            reporter.warning("Z3 doesn't know because: " + z3.getSearchFailure.message)
            (None, Map.empty)
          }
        })
        actualResult
      }
    }
    result
  }

  protected[purescala] var exprToZ3Id : Map[Expr,Z3AST] = Map.empty
  protected[purescala] var z3IdToExpr : Map[Z3AST,Expr] = Map.empty
  protected[purescala] def toZ3Formula(z3: Z3Context, expr: Expr, initialMap: Map[Identifier,Z3AST] = Map.empty, extraClauses : List[Z3AST] = Nil) : Option[(Z3AST, List[Z3AST])] = {
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

    var accumulatedClauses : List[Z3AST] = extraClauses

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
        case ite @ IfExpr(c, t, e) => {
          val switch = z3.mkFreshConst("path", z3.mkBoolSort)
          val placeHolder = z3.mkFreshConst("ite", typeToSort(ite.getType))
          val clause1 = z3.mkIff(switch, rec(c))
          val clause2 = z3.mkImplies(switch, z3.mkEq(placeHolder, rec(t)))
          val clause3 = z3.mkImplies(z3.mkNot(switch), z3.mkEq(placeHolder, rec(e)))

          accumulatedClauses = clause3 :: clause2 :: clause1 :: accumulatedClauses

          placeHolder
        }
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
      val res = Some((rec(expr), accumulatedClauses.reverse))
      // val usedInZ3Form = z3Vars.keys.toSet
      // println("Variables in formula:   " + varsInformula.map(_.uniqueName))
      // println("Variables passed to Z3: " + usedInZ3Form.map(_.uniqueName))

      res
    } catch {
      case e: CantTranslateException => None
    }
  }

  protected[purescala] def fromZ3Formula(tree : Z3AST) : Expr = {
    class CantTranslateException(t: Z3AST) extends Exception("Can't translate from Z3 tree: " + t)

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
        // System.exit(-1)
        throw new CantTranslateException(t)
      }
    }

    rec(tree)
  }
}

