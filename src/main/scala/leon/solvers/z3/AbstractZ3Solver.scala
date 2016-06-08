/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers.z3

import leon.utils._

import z3.scala.{Z3Solver => ScalaZ3Solver, _}
import solvers._
import purescala.Common._
import purescala.Definitions._
import purescala.Constructors._
import purescala.Extractors._
import purescala.Expressions._
import purescala.TypeOps._
import purescala.ExprOps._
import purescala.Types._

case class UnsoundExtractionException(ast: Z3AST, msg: String)
  extends Exception("Can't extract " + ast + " : " + msg)

// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait AbstractZ3Solver extends Z3Solver {

  val program : Program

  val library = program.library

  context.interruptManager.registerForInterrupts(this)

  private[this] var freed = false
  val traceE = new Exception()

  protected def unsound(ast: Z3AST, msg: String): Nothing =
    throw UnsoundExtractionException(ast, msg)

  override def finalize() {
    if (!freed) {
      println("!! Solver "+this.getClass.getName+"["+this.hashCode+"] not freed properly prior to GC:")
      traceE.printStackTrace()
      free()
    }
  }

  protected var z3 : Z3Context = new Z3Context(
    "MODEL"             -> true,
    "TYPE_CHECK"        -> true,
    "WELL_SORTED_CHECK" -> true
  )

  // @nv: This MUST take place AFTER Z3Context was created!!
  // Well... actually maybe not, but let's just leave it here to be sure
  toggleWarningMessages(true)

  protected var solver : ScalaZ3Solver = null

  override def free(): Unit = {
    freed = true
    if (z3 ne null) {
      z3.delete()
      z3 = null
    }
  }

  override def interrupt(): Unit = {
    if(z3 ne null) {
      z3.interrupt()
    }
  }

  override def recoverInterrupt(): Unit = ()

  def functionDefToDecl(tfd: TypedFunDef): Z3FuncDecl = {
    functions.cachedB(tfd) {
      val sortSeq    = tfd.params.map(vd => typeToSort(vd.getType))
      val returnSort = typeToSort(tfd.returnType)

      z3.mkFreshFuncDecl(tfd.id.uniqueName, sortSeq, returnSort)
    }
  }

  // ADT Manager
  protected val adtManager = new ADTManager(context)

  // Bijections between Leon Types/Functions/Ids to Z3 Sorts/Decls/ASTs
  protected val functions = new IncrementalBijection[TypedFunDef, Z3FuncDecl]()
  protected val lambdas   = new IncrementalBijection[FunctionType, Z3FuncDecl]()
  protected val variables = new IncrementalBijection[Expr, Z3AST]()

  protected val constructors = new IncrementalBijection[TypeTree, Z3FuncDecl]()
  protected val selectors    = new IncrementalBijection[(TypeTree, Int), Z3FuncDecl]()
  protected val testers      = new IncrementalBijection[TypeTree, Z3FuncDecl]()

  protected val sorts     = new IncrementalMap[TypeTree, Z3Sort]()

  var isInitialized = false
  protected[leon] def initZ3(): Unit = {
    if (!isInitialized) {
      solver = z3.mkSolver()

      functions.clear()
      lambdas.clear()
      variables.clear()
      constructors.clear()
      selectors.clear()
      testers.clear()
      sorts.reset()

      prepareSorts()

      isInitialized = true
    }
  }

  initZ3()

  def rootType(ct: TypeTree): TypeTree = ct match {
    case ct: ClassType => ct.root
    case t => t
  }

  def declareStructuralSort(t: TypeTree): Z3Sort = {
    //println("///"*40)
    //println("Declaring for: "+t)

    adtManager.defineADT(t) match {
      case Left(adts) =>
        declareDatatypes(adts.toSeq)
        sorts(normalizeType(t))

      case Right(conflicts) =>
        conflicts.foreach { declareStructuralSort }
        declareStructuralSort(t)
    }
  }

  def declareDatatypes(adts: Seq[(TypeTree, DataType)]): Unit = {
    import Z3Context.{ADTSortReference, RecursiveType, RegularSort}

    val indexMap: Map[TypeTree, Int] = adts.map(_._1).zipWithIndex.toMap

    def typeToSortRef(tt: TypeTree): ADTSortReference = {
      val tpe = rootType(tt)

      if (indexMap contains tpe) {
        RecursiveType(indexMap(tpe))
      } else {
        RegularSort(typeToSort(tt))
      }
    }

    // Define stuff
    val defs = for ((_, DataType(sym, cases)) <- adts) yield {(
      sym.uniqueName,
      cases.map(c => c.sym.uniqueName),
      cases.map(c => c.fields.map { case(id, tpe) => (id.uniqueName, typeToSortRef(tpe))})
    )}

    val resultingZ3Info = z3.mkADTSorts(defs)

    for ((z3Inf, (tpe, DataType(sym, cases))) <- resultingZ3Info zip adts) {
      sorts += (tpe -> z3Inf._1)
      assert(cases.size == z3Inf._2.size)

      for ((c, (consFun, testFun)) <- cases zip (z3Inf._2 zip z3Inf._3)) {
        testers += (c.tpe -> testFun)
        constructors += (c.tpe -> consFun)
      }

      for ((c, fieldFuns) <- cases zip z3Inf._4) {
        assert(c.fields.size == fieldFuns.size)

        for ((selFun, index) <- fieldFuns.zipWithIndex) {
          selectors += (c.tpe, index) -> selFun
        }
      }
    }
  }

  // Prepares some of the Z3 sorts, but *not* the tuple sorts; these are created on-demand.
  private def prepareSorts(): Unit = {

    z3.mkADTSorts(
      Seq((
        "Unit",
        Seq("Unit"),
        Seq(Seq())
      ))
    )

    //TODO: mkBitVectorType
    sorts += Int32Type -> z3.mkBVSort(32)
    sorts += CharType -> z3.mkBVSort(32)
    sorts += IntegerType -> z3.mkIntSort
    sorts += RealType -> z3.mkRealSort
    sorts += BooleanType -> z3.mkBoolSort

    testers.clear()
    constructors.clear()
    selectors.clear()
  }

  def normalizeType(t: TypeTree): TypeTree = {
    bestRealType(t)
  }

  // assumes prepareSorts has been called....
  protected[leon] def typeToSort(oldtt: TypeTree): Z3Sort = normalizeType(oldtt) match {
    case Int32Type | BooleanType | IntegerType | RealType | CharType =>
      sorts(oldtt)

    case tpe @ (_: ClassType  | _: ArrayType | _: TupleType | _: TypeParameter | UnitType) =>
      sorts.cached(tpe) {
        declareStructuralSort(tpe)
      }

    case tt @ SetType(base) =>
      sorts.cached(tt) {
        z3.mkSetSort(typeToSort(base))
      }

    case tt @ MapType(fromType, toType) =>
      typeToSort(RawArrayType(fromType, library.optionType(toType)))

    case tt @ BagType(base) =>
      typeToSort(RawArrayType(base, IntegerType))

    case rat @ RawArrayType(from, to) =>
      sorts.cached(rat) {
        val fromSort = typeToSort(from)
        val toSort = typeToSort(to)

        z3.mkArraySort(fromSort, toSort)
      }

    case ft @ FunctionType(from, to) =>
      sorts.cached(ft) {
        val symbol = z3.mkFreshStringSymbol(ft.toString)
        z3.mkUninterpretedSort(symbol)
      }

    case other =>
      unsupported(other)
  }

  protected[leon] def toZ3Formula(expr: Expr, initialMap: Map[Identifier, Z3AST] = Map.empty): Z3AST = {

    var z3Vars: Map[Identifier,Z3AST] = if (initialMap.nonEmpty) {
      initialMap
    } else {
      // FIXME TODO pleeeeeeeease make this cleaner. Ie. decide what set of
      // variable has to remain in a map etc.
      variables.aToB.collect{ case (Variable(id), p2) => id -> p2 }
    }

    def rec(ex: Expr): Z3AST = ex match {

      // TODO: Leave that as a specialization?
      case LetTuple(ids, e, b) =>
        z3Vars = z3Vars ++ ids.zipWithIndex.map { case (id, ix) =>
          val entry = id -> rec(tupleSelect(e, ix + 1, ids.size))
          entry
        }
        val rb = rec(b)
        z3Vars = z3Vars -- ids
        rb

      case p @ Passes(_, _, _) =>
        rec(p.asConstraint)

      case me @ MatchExpr(s, cs) =>
        rec(matchToIfThenElse(me))

      case Let(i, e, b) =>
        val re = rec(e)
        z3Vars = z3Vars + (i -> re)
        val rb = rec(b)
        z3Vars = z3Vars - i
        rb

      case a @ Assert(cond, err, body) =>
        rec(IfExpr(cond, body, Error(a.getType, err.getOrElse("Assertion failed")).setPos(a.getPos)).setPos(a.getPos))

      case e @ Error(tpe, _) =>
        val newAST = z3.mkFreshConst("errorValue", typeToSort(tpe))
        // Might introduce dupplicates (e), but no worries here
        variables += (e -> newAST)
        newAST

      case v @ Variable(id) => z3Vars.getOrElse(id,
        variables.getB(v).getOrElse {
          val newAST = z3.mkFreshConst(id.uniqueName, typeToSort(v.getType))
          z3Vars = z3Vars + (id -> newAST)
          variables += (v -> newAST)
          newAST
        }
      )

      case ite @ IfExpr(c, t, e) => z3.mkITE(rec(c), rec(t), rec(e))
      case And(exs) => z3.mkAnd(exs.map(rec): _*)
      case Or(exs) => z3.mkOr(exs.map(rec): _*)
      case Implies(l, r) => z3.mkImplies(rec(l), rec(r))
      case Not(Equals(l, r)) => z3.mkDistinct(rec(l), rec(r))
      case Not(e) => z3.mkNot(rec(e))
      case IntLiteral(v) => z3.mkInt(v, typeToSort(Int32Type))
      case InfiniteIntegerLiteral(v) => z3.mkNumeral(v.toString, typeToSort(IntegerType))
      case FractionalLiteral(n, d) => z3.mkNumeral(s"$n / $d", typeToSort(RealType))
      case CharLiteral(c) => z3.mkInt(c, typeToSort(CharType))
      case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
      case Equals(l, r) => z3.mkEq(rec( l ), rec( r ) )
      case Plus(l, r) => z3.mkAdd(rec(l), rec(r))
      case Minus(l, r) => z3.mkSub(rec(l), rec(r))
      case Times(l, r) => z3.mkMul(rec(l), rec(r))
      case Division(l, r) =>
        val rl = rec(l)
        val rr = rec(r)
        z3.mkITE(
          z3.mkGE(rl, z3.mkNumeral("0", typeToSort(IntegerType))),
          z3.mkDiv(rl, rr),
          z3.mkUnaryMinus(z3.mkDiv(z3.mkUnaryMinus(rl), rr))
        )
      case Remainder(l, r) =>
        val q = rec(Division(l, r))
        z3.mkSub(rec(l), z3.mkMul(rec(r), q))
      case Modulo(l, r) =>
        z3.mkMod(rec(l), rec(r))
      case UMinus(e) => z3.mkUnaryMinus(rec(e))

      case RealPlus(l, r) => z3.mkAdd(rec(l), rec(r))
      case RealMinus(l, r) => z3.mkSub(rec(l), rec(r))
      case RealTimes(l, r) => z3.mkMul(rec(l), rec(r))
      case RealDivision(l, r) => z3.mkDiv(rec(l), rec(r))
      case RealUMinus(e) => z3.mkUnaryMinus(rec(e))

      case BVPlus(l, r) => z3.mkBVAdd(rec(l), rec(r))
      case BVMinus(l, r) => z3.mkBVSub(rec(l), rec(r))
      case BVTimes(l, r) => z3.mkBVMul(rec(l), rec(r))
      case BVDivision(l, r) => z3.mkBVSdiv(rec(l), rec(r))
      case BVRemainder(l, r) => z3.mkBVSrem(rec(l), rec(r))
      case BVUMinus(e) => z3.mkBVNeg(rec(e))
      case BVNot(e) => z3.mkBVNot(rec(e))
      case BVAnd(l, r) => z3.mkBVAnd(rec(l), rec(r))
      case BVOr(l, r) => z3.mkBVOr(rec(l), rec(r))
      case BVXOr(l, r) => z3.mkBVXor(rec(l), rec(r))
      case BVShiftLeft(l, r) => z3.mkBVShl(rec(l), rec(r))
      case BVAShiftRight(l, r) => z3.mkBVAshr(rec(l), rec(r))
      case BVLShiftRight(l, r) => z3.mkBVLshr(rec(l), rec(r))
      case LessThan(l, r) => l.getType match {
        case IntegerType => z3.mkLT(rec(l), rec(r))
        case RealType => z3.mkLT(rec(l), rec(r))
        case Int32Type => z3.mkBVSlt(rec(l), rec(r))
        case CharType => z3.mkBVSlt(rec(l), rec(r))
      }
      case LessEquals(l, r) => l.getType match {
        case IntegerType => z3.mkLE(rec(l), rec(r))
        case RealType => z3.mkLE(rec(l), rec(r))
        case Int32Type => z3.mkBVSle(rec(l), rec(r))
        case CharType => z3.mkBVSle(rec(l), rec(r))
        //case _ => throw new IllegalStateException(s"l: $l, Left type: ${l.getType} Expr: $ex")
      }
      case GreaterThan(l, r) => l.getType match {
        case IntegerType => z3.mkGT(rec(l), rec(r))
        case RealType => z3.mkGT(rec(l), rec(r))
        case Int32Type => z3.mkBVSgt(rec(l), rec(r))
        case CharType => z3.mkBVSgt(rec(l), rec(r))
      }
      case GreaterEquals(l, r) => l.getType match {
        case IntegerType => z3.mkGE(rec(l), rec(r))
        case RealType => z3.mkGE(rec(l), rec(r))
        case Int32Type => z3.mkBVSge(rec(l), rec(r))
        case CharType => z3.mkBVSge(rec(l), rec(r))
      }

      case u : UnitLiteral =>
        val tpe = normalizeType(u.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor()

      case t @ Tuple(es) =>
        val tpe = normalizeType(t.getType)
        typeToSort(tpe)
        val constructor = constructors.toB(tpe)
        constructor(es.map(rec): _*)

      case ts @ TupleSelect(t, i) =>
        val tpe = normalizeType(t.getType)
        typeToSort(tpe)
        val selector = selectors.toB((tpe, i-1))
        selector(rec(t))

      case c @ CaseClass(ct, args) =>
        typeToSort(ct) // Making sure the sort is defined
        val constructor = constructors.toB(ct)
        constructor(args.map(rec): _*)

      case c @ CaseClassSelector(cct, cc, sel) =>
        typeToSort(cct) // Making sure the sort is defined
        val selector = selectors.toB(cct, c.selectorIndex)
        selector(rec(cc))

      case AsInstanceOf(expr, ct) =>
        rec(expr)

      case IsInstanceOf(e, act: AbstractClassType) =>
        act.knownCCDescendants match {
          case Seq(cct) =>
            rec(IsInstanceOf(e, cct))
          case more =>
            val i = FreshIdentifier("e", act, alwaysShowUniqueID = true)
            rec(Let(i, e, orJoin(more map(IsInstanceOf(Variable(i), _)))))
        }

      case IsInstanceOf(e, cct: CaseClassType) =>
        typeToSort(cct) // Making sure the sort is defined
        val tester = testers.toB(cct)
        tester(rec(e))

      case f @ FunctionInvocation(tfd, args) =>
        z3.mkApp(functionDefToDecl(tfd), args.map(rec): _*)

      case fa @ Application(caller, args) =>
        val ft @ FunctionType(froms, to) = normalizeType(caller.getType)
        val funDecl = lambdas.cachedB(ft) {
          val sortSeq    = (ft +: froms).map(tpe => typeToSort(tpe))
          val returnSort = typeToSort(to)

          val name = FreshIdentifier("dynLambda").uniqueName
          z3.mkFreshFuncDecl(name, sortSeq, returnSort)
        }
        z3.mkApp(funDecl, (caller +: args).map(rec): _*)

      case ElementOfSet(e, s) => z3.mkSetMember(rec(e), rec(s))
      case SubsetOf(s1, s2) => z3.mkSetSubset(rec(s1), rec(s2))
      case SetIntersection(s1, s2) => z3.mkSetIntersect(rec(s1), rec(s2))
      case SetUnion(s1, s2) => z3.mkSetUnion(rec(s1), rec(s2))
      case SetDifference(s1, s2) => z3.mkSetDifference(rec(s1), rec(s2))
      case f @ FiniteSet(elems, base) => elems.foldLeft(z3.mkEmptySet(typeToSort(base)))((ast, el) => z3.mkSetAdd(ast, rec(el)))

      case fb @ FiniteBag(elems, base) =>
        typeToSort(fb.getType)
        rec(RawArrayValue(base, elems, InfiniteIntegerLiteral(0)))

      case BagAdd(b, e) =>
        val bag = rec(b)
        val elem = rec(e)
        z3.mkStore(bag, elem, z3.mkAdd(z3.mkSelect(bag, elem), rec(InfiniteIntegerLiteral(1))))

      case MultiplicityInBag(e, b) =>
        z3.mkSelect(rec(b), rec(e))

      case BagUnion(b1, b2) =>
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType), typeToSort(IntegerType))
        z3.mkArrayMap(plus, rec(b1), rec(b2))

      case BagIntersection(b1, b2) =>
        rec(BagDifference(b1, BagDifference(b1, b2)))

      case BagDifference(b1, b2) =>
        val abs = z3.getAbsFuncDecl()
        val plus = z3.getFuncDecl(OpAdd, typeToSort(IntegerType), typeToSort(IntegerType))
        val minus = z3.getFuncDecl(OpSub, typeToSort(IntegerType), typeToSort(IntegerType))
        val div = z3.getFuncDecl(OpDiv, typeToSort(IntegerType), typeToSort(IntegerType))

        val all2 = z3.mkConstArray(typeToSort(IntegerType), z3.mkInt(2, typeToSort(IntegerType)))
        val withNeg = z3.mkArrayMap(minus, rec(b1), rec(b2))
        z3.mkArrayMap(div, z3.mkArrayMap(plus, withNeg, z3.mkArrayMap(abs, withNeg)), all2)

      case al @ RawArraySelect(a, i) =>
        z3.mkSelect(rec(a), rec(i))
      case al @ RawArrayUpdated(a, i, e) =>
        z3.mkStore(rec(a), rec(i), rec(e))
      case RawArrayValue(keyTpe, elems, default) =>
        val ar = z3.mkConstArray(typeToSort(keyTpe), rec(default))

        elems.foldLeft(ar) {
          case (array, (k, v)) => z3.mkStore(array, rec(k), rec(v))
        }

      /**
       * ===== Map operations =====
       */
      case m @ FiniteMap(elems, from, to) =>
        val MapType(_, t) = normalizeType(m.getType)

        rec(RawArrayValue(from, elems.map{
          case (k, v) => (k, CaseClass(library.someType(t), Seq(v)))
        }, CaseClass(library.noneType(t), Seq())))

      case MapApply(m, k) =>
        val mt @ MapType(_, t) = normalizeType(m.getType)
        typeToSort(mt)

        val el = z3.mkSelect(rec(m), rec(k))

        // Really ?!? We don't check that it is actually != None?
        selectors.toB(library.someType(t), 0)(el)

      case MapIsDefinedAt(m, k) =>
        val mt @ MapType(_, t) = normalizeType(m.getType)
        typeToSort(mt)

        val el = z3.mkSelect(rec(m), rec(k))

        testers.toB(library.someType(t))(el)

      case MapUnion(m1, FiniteMap(elems, _, _)) =>
        val mt @ MapType(_, t) = normalizeType(m1.getType)
        typeToSort(mt)

        elems.foldLeft(rec(m1)) { case (m, (k,v)) =>
          z3.mkStore(m, rec(k), rec(CaseClass(library.someType(t), Seq(v))))
        }

      case gv @ GenericValue(tp, id) =>
        typeToSort(tp)
        val constructor = constructors.toB(tp)
        constructor(rec(InfiniteIntegerLiteral(id)))

      case synthesis.utils.MutableExpr(ex) =>
        rec(ex)

      case other =>
        unsupported(other)
    }

    rec(expr)
  }

  protected[leon] def fromZ3Formula(model: Z3Model, tree: Z3AST, tpe: TypeTree): Expr = {

    def rec(t: Z3AST, tpe: TypeTree): Expr = {
      val kind = z3.getASTKind(t)
      kind match {
        case Z3NumeralIntAST(Some(v)) =>
          val leading = t.toString.substring(0, 2 min t.toString.length)
          if(leading == "#x") {
            _root_.smtlib.common.Hexadecimal.fromString(t.toString.substring(2)) match {
              case Some(hexa) =>
                tpe match {
                  case Int32Type => IntLiteral(hexa.toInt)
                  case CharType  => CharLiteral(hexa.toInt.toChar)
                  case IntegerType => InfiniteIntegerLiteral(BigInt(hexa.toInt))
                  case other =>
                    unsupported(other, "Unexpected target type for BV value")
                }
              case None => unsound(t, "could not translate hexadecimal Z3 numeral")
              }
          } else {
            tpe match {
              case Int32Type => IntLiteral(v)
              case CharType  => CharLiteral(v.toChar)
              case IntegerType => InfiniteIntegerLiteral(BigInt(v))
              case other =>
                unsupported(other, "Unexpected type for BV value: " + other)
            } 
          }

        case Z3NumeralIntAST(None) =>
          val ts = t.toString
          reporter.ifDebug(printer => printer(ts))(DebugSectionSynthesis)
          if(ts.length > 4 && ts.substring(0, 2) == "bv" && ts.substring(ts.length - 4) == "[32]") {
            val integer = ts.substring(2, ts.length - 4)
            tpe match {
              case Int32Type => 
                IntLiteral(integer.toLong.toInt)
              case CharType  => CharLiteral(integer.toInt.toChar)
              case IntegerType => 
                InfiniteIntegerLiteral(BigInt(integer))
              case _ =>
                reporter.fatalError("Unexpected target type for BV value: " + tpe.asString)
            }
          } else {  
            _root_.smtlib.common.Hexadecimal.fromString(t.toString.substring(2)) match {
              case Some(hexa) =>
                tpe match {
                  case Int32Type => IntLiteral(hexa.toInt)
                  case CharType  => CharLiteral(hexa.toInt.toChar)
                  case _ => unsound(t, "unexpected target type for BV value: " + tpe.asString)
                }
              case None => unsound(t, "could not translate Z3NumeralIntAST numeral")
            }
          }

        case Z3NumeralRealAST(n: BigInt, d: BigInt) => FractionalLiteral(n, d)

        case Z3AppAST(decl, args) =>
          val argsSize = args.size
          if (argsSize == 0 && (variables containsB t)) {
            variables.toA(t)
          } else if(functions containsB decl) {
            val tfd = functions.toA(decl)
            assert(tfd.params.size == argsSize)
            FunctionInvocation(tfd, args.zip(tfd.params).map{ case (a, p) => rec(a, p.getType) })
          } else if (constructors containsB decl) {
            constructors.toA(decl) match {
              case cct: CaseClassType =>
                CaseClass(cct, args.zip(cct.fieldsTypes).map { case (a, t) => rec(a, t) })

              case UnitType =>
                UnitLiteral()

              case TupleType(ts) =>
                tupleWrap(args.zip(ts).map { case (a, t) => rec(a, t) })

              case ArrayType(to) =>
                val size = rec(args(0), Int32Type)
                val map  = rec(args(1), RawArrayType(Int32Type, to))

                (size, map) match {

                  case (s : IntLiteral, RawArrayValue(_, elems, default)) =>

                    if (s.value < 0)
                      unsupported(s, s"Z3 returned array of negative size")

                    val entries = elems.map {
                      case (IntLiteral(i), v) => i -> v
                      case (e,_) => unsupported(e, s"Z3 returned unexpected array index ${e.asString}")
                    }

                    finiteArray(entries, Some(default, s), to)
                  case (s : IntLiteral, arr) => unsound(args(1), "invalid array type")
                  case (size, _) => unsound(args(0), "invalid array size")
                }

              case tp @ TypeParameter(id) =>
                val InfiniteIntegerLiteral(n) = rec(args(0), IntegerType)
                GenericValue(tp, n.toInt)

              case t =>
                unsupported(t, "Woot? structural type that is non-structural")
            }
          } else {
            tpe match {
              case RawArrayType(from, to) =>
                model.getArrayValue(t) match {
                  case Some((z3map, z3default)) =>
                    val default = rec(z3default, to)
                    val entries = z3map.map {
                      case (k,v) => (rec(k, from), rec(v, to))
                    }

                    RawArrayValue(from, entries, default)
                  case None => unsound(t, "invalid array AST")
                }

              case ft @ FunctionType(fts, tt) => lambdas.getB(ft) match {
                case None => simplestValue(ft)
                case Some(decl) => model.getFuncInterpretations.find(_._1 == decl) match {
                  case None => simplestValue(ft)
                  case Some((_, mapping, elseValue)) =>
                    val leonElseValue = rec(elseValue, tt)
                    FiniteLambda(mapping.flatMap { case (z3Args, z3Result) =>
                      if (t == z3Args.head) {
                        List((z3Args.tail zip fts).map(p => rec(p._1, p._2)) -> rec(z3Result, tt))
                      } else {
                        Nil
                      }
                    }, leonElseValue, ft)
                }
              }

              case MapType(from, to) =>
                rec(t, RawArrayType(from, library.optionType(to))) match {
                  case r: RawArrayValue =>
                    // We expect a RawArrayValue with keys in from and values in Option[to],
                    // with default value == None
                    if (r.default.getType != library.noneType(to)) {
                      unsupported(r, "Solver returned a co-finite map which is not supported.")
                    }
                    require(r.keyTpe == from, s"Type error in solver model, expected ${from.asString}, found ${r.keyTpe.asString}")

                    val elems = r.elems.flatMap {
                      case (k, CaseClass(leonSome, Seq(x))) => Some(k -> x)
                      case (k, _) => None
                    }

                    FiniteMap(elems, from, to)
                }

              case BagType(base) =>
                val r @ RawArrayValue(_, elems, default) = rec(t, RawArrayType(base, IntegerType))
                if (default != InfiniteIntegerLiteral(0)) {
                  unsupported(r, "Solver returned a co-finite bag which is not supported.")
                }

                FiniteBag(elems, base)

              case tpe @ SetType(dt) =>
                model.getSetValue(t) match {
                  case None => unsound(t, "invalid set AST")
                  case Some((_, false)) => unsound(t, "co-finite set AST")
                  case Some((set, true)) =>
                    val elems = set.map(e => rec(e, dt))
                    FiniteSet(elems, dt)
                }

              case _ =>
                import Z3DeclKind._
                z3.getDeclKind(decl) match {
                  case OpTrue =>    BooleanLiteral(true)
                  case OpFalse =>   BooleanLiteral(false)
            //      case OpEq =>      Equals(rargs(0), rargs(1))
            //      case OpITE =>     IfExpr(rargs(0), rargs(1), rargs(2))
            //      case OpAnd =>     andJoin(rargs)
            //      case OpOr =>      orJoin(rargs)
            //      case OpIff =>     Equals(rargs(0), rargs(1))
            //      case OpXor =>     not(Equals(rargs(0), rargs(1)))
            //      case OpNot =>     not(rargs(0))
            //      case OpImplies => implies(rargs(0), rargs(1))
            //      case OpLE =>      LessEquals(rargs(0), rargs(1))
            //      case OpGE =>      GreaterEquals(rargs(0), rargs(1))
            //      case OpLT =>      LessThan(rargs(0), rargs(1))
            //      case OpGT =>      GreaterThan(rargs(0), rargs(1))
            //      case OpAdd =>     Plus(rargs(0), rargs(1))
            //      case OpSub =>     Minus(rargs(0), rargs(1))
                  case OpUMinus =>  UMinus(rec(args(0), tpe))
            //      case OpMul =>     Times(rargs(0), rargs(1))
            //      case OpDiv =>     Division(rargs(0), rargs(1))
            //      case OpIDiv =>    Division(rargs(0), rargs(1))
            //      case OpMod =>     Modulo(rargs(0), rargs(1))
                  case other => unsound(t, 
                      s"""|Don't know what to do with this declKind: $other
                          |Expected type: ${Option(tpe).map{_.asString}.getOrElse("")}
                          |Tree: $t
                          |The arguments are: $args""".stripMargin
                    )
                }
            }
          }
        case _ => unsound(t, "unexpected AST")
      }
    }

    rec(tree, normalizeType(tpe))
  }

  protected[leon] def softFromZ3Formula(model: Z3Model, tree: Z3AST, tpe: TypeTree) : Option[Expr] = {
    try {
      Some(fromZ3Formula(model, tree, tpe))
    } catch {
      case e: Unsupported => None
      case e: UnsoundExtractionException => None
      case n: java.lang.NumberFormatException => None
    }
  }

  def idToFreshZ3Id(id: Identifier): Z3AST = {
    z3.mkFreshConst(id.uniqueName, typeToSort(id.getType))
  }

  def reset(): Unit = {
    throw new CantResetException(this)
  }

}
