/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._
import scala.tools.nsc.plugins._

import scala.language.implicitConversions

import purescala._
import purescala.Definitions.{ClassDef => LeonClassDef, ModuleDef => LeonModuleDef, _}
import purescala.Trees.{Expr => LeonExpr, _}
import purescala.TypeTrees.{TypeTree => LeonType, _}
import purescala.Common._
import purescala.TreeOps._
import purescala.TypeTreeOps._
import xlang.Trees.{Block => LeonBlock, _}
import xlang.TreeOps._

import utils.{Position => LeonPosition, OffsetPosition => LeonOffsetPosition, RangePosition => LeonRangePosition}

trait CodeExtraction extends ASTExtractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import ExtractorHelpers._

  implicit def scalaPosToLeonPos(p: global.Position): LeonPosition = {
    if (p.isRange) {
      val start = p.focusStart
      val end   = p.focusEnd
      LeonRangePosition(start.line, start.column, start.point,
                        end.line, end.column, end.point,
                        p.source.file.file)
    } else {
      LeonOffsetPosition(p.line, p.column, p.point,
                         p.source.file.file)
    }
  }

  private val mutableVarSubsts: scala.collection.mutable.Map[Symbol,Function0[LeonExpr]] =
    scala.collection.mutable.Map.empty[Symbol,Function0[LeonExpr]]

  private var classesToClasses = Map[Symbol, LeonClassDef]()
  private var defsToDefs = Map[Symbol, FunDef]()
  private var varSubsts = Map[Symbol, () => LeonExpr]()

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed case class ImpureCodeEncounteredException(tree: Tree) extends Exception

  /** Attempts to convert a scalac AST to a pure scala AST. */
  private var currentFunDef: FunDef = null

  //This is a bit missleading, if an expr is not mapped then it has no owner, if it is mapped to None it means
  //that it can have any owner
  private var owners: Map[Identifier, Option[FunDef]] = Map() 


  class Extraction(unit: CompilationUnit) {

    def toPureScala(tree: Tree)(implicit dctx: DefContext): Option[LeonExpr] = {
      try {
        Some(extractTree(tree))
      } catch {
        case e: ImpureCodeEncounteredException =>
          None
      }
    }

    // This one never fails, on error, it returns Untyped
    def toPureScalaType(tpt: Type)(implicit dctx: DefContext): LeonType = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          Untyped
      }
    }

    private def extractTopLevelDef: Option[LeonModuleDef] = {
      unit.body match {
        case p @ PackageDef(name, lst) if lst.size == 0 =>
          reporter.error(p.pos, "No top-level definition found.")
          None

        case PackageDef(name, lst) =>
          if (lst.size > 1) {
           reporter.error(lst(1).pos, "More than one top-level object. Rest will be ignored.")
          }
          lst(0) match {
            case ExObjectDef(n, templ) =>
              Some(extractObjectDef(n.toString, templ))

            case other @ _ =>
              reporter.error(other.pos, "Expected: top-level single object.")
              None
          }
        }
    }

    case class DefContext(
      tparams: Map[Symbol, TypeParameter]
    )

    private def extractTypeParams(tps: Seq[Type]): Seq[(Symbol, TypeParameter)] = {
      tps.flatMap {
        case TypeRef(_, sym, Nil) =>
          Some(sym -> TypeParameter(FreshIdentifier(sym.name.toString)))
        case t =>
          reporter.error(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
          None
      }
    }

    private def extractObjectDef(nameStr: String, tmpl: Template): LeonModuleDef = {
      // we assume that the template actually corresponds to an object
      // definition. Typically it should have been obtained from the proper
      // extractor (ExObjectDef)


      var seenClasses  = Map[Symbol, Seq[(String, Tree)]]()

      def extractClass(sym: Symbol): LeonClassDef = {
        classesToClasses.get(sym) match {
          case Some(cd) => cd
          case None =>
            val id = FreshIdentifier(sym.name.toString).setPos(sym.pos)

            val tparamsMap = sym.tpe match {
              case TypeRef(_, _, tps) =>
                extractTypeParams(tps)
              case _ =>
                Nil
            }

            val tparams = tparamsMap.map(t => TypeParameterDef(t._2))

            val defCtx = DefContext(tparamsMap.toMap)

            val parent = sym.tpe.parents.headOption match {
              case Some(TypeRef(_, parentSym, tps)) if seenClasses.contains(parentSym) =>
                extractClass(parentSym) match {
                  case acd :AbstractClassDef =>
                    val newTps = tps.map(extractType(_)(defCtx))
                    Some(AbstractClassType(acd, newTps))

                  case cd =>
                    reporter.error(sym.pos, "Class "+id+" cannot extend "+cd.id)
                    None
                }

              case _ =>
                None
            }

            if (sym.isAbstractClass) {
              val acd = AbstractClassDef(id, tparams, parent).setPos(sym.pos)

              classesToClasses += sym -> acd

              acd
            } else {
              val ccd = CaseClassDef(id, tparams, parent, sym.isModuleClass).setPos(sym.pos)

              parent.foreach(_.classDef.registerChildren(ccd))

              classesToClasses += sym -> ccd

              // Validates type parameters
              parent match {
                case Some(pct) =>
                  if(pct.classDef.tparams.size == tparams.size) {
                    val pcd = pct.classDef
                    val ptps = pcd.tparams.map(_.tp)

                    val targetType = AbstractClassType(pcd, ptps)
                    val fromChild = CaseClassType(ccd, ptps).parent.get

                    if (fromChild != targetType) {
                      reporter.error(sym.pos, "Child type should form a simple bijection with parent class type (e.g. C[T1,T2] extends P[T1,T2])")
                    }

                  } else {
                    reporter.error(sym.pos, "Child classes should have the same number of type parameters as their parent")
                  }
                case _ =>
              }

              ccd
            }
        }
      }

      // We collect all defined classes
      for (t <- tmpl.body) t match {
        case ExAbstractClass(o2, sym) =>
          seenClasses += sym -> Nil

        case ExCaseClass(o2, sym, args) =>
          seenClasses += sym -> args

        case _ =>
      }

      // Pass 2: we define classDefs
      for ((sym, params) <- seenClasses) {
        extractClass(sym)
      }

      // Pass 3: we define fields
      for ((sym, params) <- seenClasses) {
        extractClass(sym) match {
          case ccd: CaseClassDef =>
            val tparamsSym = sym.tpe match {
              case TypeRef(_, _, tps) =>
                extractTypeParams(tps).map(_._1)
              case _ =>
                Nil
            }

            val tparamsMap = (tparamsSym zip ccd.tparams.map(_.tp)).toMap

            val defCtx = DefContext(tparamsMap)

            val fields = params.map { case (aname, asym) =>
              val tpe = toPureScalaType(asym.tpe)(defCtx)
              VarDecl(FreshIdentifier(aname).setType(tpe).setPos(asym.pos), tpe).setPos(asym.pos)
            }
            ccd.setFields(fields)
          case _ =>
        }
      }

      // First pass to instanciate all FunDefs
      for (d <- tmpl.body) d match {
        case ExMainFunctionDef() =>
          // we ignore the main function

        case dd @ ExFunctionDef(sym, tparams, params, ret, body) =>
          val dctx = DefContext(Map())

          val funDef = extractFunSig(sym, tparams, params, ret)(dctx)

          if (dd.mods.isPrivate) {
            funDef.addAnnotation("private")
          }

          for(a <- dd.symbol.annotations) {
            a.atp.safeToString match {
              case "leon.Annotations.induct"     => funDef.addAnnotation("induct")
              case "leon.Annotations.axiomatize" => funDef.addAnnotation("axiomatize")
              case "leon.Annotations.main"       => funDef.addAnnotation("main")
              case _ => ;
            }
          }

          defsToDefs += dd.symbol -> funDef

        case _ =>
      }

      // Second pass to convert function bodies
      for (d <- tmpl.body) d match {
        case ExFunctionDef(sym, tparams, _, _, body) if defsToDefs contains sym =>
          val fd = defsToDefs(sym).setPos(d.pos)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          val dctx = DefContext(tparamsMap)
          extractFunDef(fd, body)(dctx)
        case _ =>
      }

      var funDefs: List[FunDef] = defsToDefs.values.toList

      // FIXME: we check nothing else is polluting the object
      for (t <- tmpl.body) t match {
        case ExCaseClassSyntheticJunk() =>
        case ExAbstractClass(_,_) =>
        case ExCaseClass(_,_,_) =>
        case ExConstructorDef() =>
        case ExMainFunctionDef() =>
        case ExFunctionDef(_, _, _, _, _) =>
        case tree =>
          unsupported(tree, "Don't know what to do with this. Not purescala?");
      }

      new LeonModuleDef(FreshIdentifier(nameStr), classesToClasses.values.toList ::: funDefs, Nil)
    }

    private def extractFunSig(sym: Symbol, tps: Seq[Symbol], params: Seq[ValDef], ret: Type)(implicit dctx: DefContext): FunDef = {

      val tparams = extractTypeParams(tps.map(_.tpe))

      val dctx = DefContext(tparams.toMap)

      val newParams = params.map{ vd =>
        val ptpe = toPureScalaType(vd.tpt.tpe)(dctx)
        val newID = FreshIdentifier(vd.symbol.name.toString).setType(ptpe).setPos(vd.pos)
        owners += (newID -> None)
        varSubsts += vd.symbol -> (() => Variable(newID))
        VarDecl(newID, ptpe).setPos(vd.pos)
      }

      val tparamsDef = tparams.map(t => TypeParameterDef(t._2))

      new FunDef(FreshIdentifier(sym.name.toString), tparamsDef, toPureScalaType(ret)(dctx), newParams)
    }

    private def extractFunDef(funDef: FunDef, body: Tree)(implicit dctx: DefContext): FunDef = {
      currentFunDef = funDef

      val (body2, ensuring) = body match {
        case ExEnsuredExpression(body2, resSym, contract) =>
          val resId = FreshIdentifier(resSym.name.toString).setType(funDef.returnType).setPos(resSym.pos)
          varSubsts += resSym -> (() => Variable(resId))
          (body2, toPureScala(contract).map(r => (resId, r)))

        case ExHoldsExpression(body2) =>
          val resId = FreshIdentifier("res").setType(BooleanType)
          (body2, Some((resId, Variable(resId))))

        case _ =>
          (body, None)
      }

      val (body3, require) = body2 match {
        case ExRequiredExpression(body3, contract) =>
          (body3, toPureScala(contract))

        case _ =>
          (body2, None)
      }

      val finalBody = try {
        toPureScala(body3).map(flattenBlocks) match {
          case Some(e) if e.getType.isInstanceOf[ArrayType] =>
            getOwner(e) match {
              case Some(Some(fd)) if fd == funDef =>
                Some(e)

              case None =>
                Some(e)

              case _ =>
                reporter.error(body3.pos, "Function cannot return an array that is not locally defined")
                None
            }
          case e =>
            e
        }
      } catch {
        case e: ImpureCodeEncounteredException =>
        None
      }

      val finalRequire = require.filter{ e =>
        if(containsLetDef(e)) {
          reporter.error(body3.pos, "Function precondtion should not contain nested function definition")
          false
        } else {
          true
        }
      }

      val finalEnsuring = ensuring.filter{ case (id, e) =>
        if(containsLetDef(e)) {
          reporter.error(body3.pos, "Function postcondition should not contain nested function definition")
          false
        } else {
          true
        }
      }

      funDef.body          = finalBody
      funDef.precondition  = finalRequire
      funDef.postcondition = finalEnsuring
      funDef
    }

    def unsupported(msg: String): Nothing = {
      reporter.error(NoPosition, msg)
      throw new ImpureCodeEncounteredException(null)
    }
    def unsupported(tr: Tree, msg: String): Nothing = {
      reporter.error(tr.pos, msg)
      reporter.error(tr.pos, tr.toString)
      throw new ImpureCodeEncounteredException(tr)
    }


    private def extractPattern(p: Tree, binder: Option[Identifier] = None)(implicit dctx: DefContext): Pattern = p match {
      case b @ Bind(name, t @ Typed(pat, tpe)) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(tpe.tpe)).setPos(b.pos)
        varSubsts += b.symbol -> (() => Variable(newID))
        extractPattern(t, Some(newID))

      case b @ Bind(name, pat) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(b.symbol.tpe)).setPos(b.pos)
        varSubsts += b.symbol -> (() => Variable(newID))
        extractPattern(pat, Some(newID))

      case t @ Typed(Ident(nme.WILDCARD), tpt) if classesToClasses.contains(t.tpe.typeSymbol) =>
        extractType(tpt.tpe) match {
          case ct: ClassType =>
            InstanceOfPattern(binder, ct).setPos(p.pos)
          case _ =>
            unsupported("Invalid type "+tpt.tpe+" for .isInstanceOf")
        }

      case Ident(nme.WILDCARD) =>
        WildcardPattern(binder).setPos(p.pos)

      case s @ Select(This(_), b) if s.tpe.typeSymbol.isCase &&
                                     classesToClasses.contains(s.tpe.typeSymbol) =>
        // case Obj =>
        extractType(s.tpe) match {
          case ct: CaseClassType =>
            assert(ct.classDef.fields.size == 0)
            CaseClassPattern(binder, ct, Seq()).setPos(p.pos)
          case _ =>
            unsupported("Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) if fn.isType &&
                                  a.tpe.typeSymbol.isCase &&
                                  classesToClasses.contains(a.tpe.typeSymbol) =>

        extractType(a.tpe) match {
          case ct: CaseClassType =>
            assert(args.size == ct.classDef.fields.size)
            CaseClassPattern(binder, ct, args.map(extractPattern(_))).setPos(p.pos)
          case _ =>
            unsupported("Invalid type "+a.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>
        extractType(a.tpe) match {
          case TupleType(argsTpes) =>
            TuplePattern(binder, args.map(extractPattern(_))).setPos(p.pos)
          case _ =>
            unsupported(p, "Unsupported pattern: "+a)
        }

      case _ =>
        unsupported(p, "Unsupported pattern: "+p)
    }

    private def extractMatchCase(cd: CaseDef)(implicit dctx: DefContext): MatchCase = {
      val recPattern = extractPattern(cd.pat)
      val recBody    = extractTree(cd.body)

      if(cd.guard == EmptyTree) {
        SimpleCase(recPattern, recBody).setPos(cd.pos)
      } else {
        val recGuard = extractTree(cd.guard)

        if(isXLang(recGuard)) {
          reporter.error(cd.guard.pos, "Guard expression must be pure")
          throw ImpureCodeEncounteredException(cd)
        }

        GuardedCase(recPattern, recGuard, recBody).setPos(cd.pos)
      }
    }

    private def extractTree(tr: Tree)(implicit dctx: DefContext): LeonExpr = {
      val (current, tmpRest) = tr match {
        case Block(Block(e :: es1, l1) :: es2, l2) =>
          (e, Some(Block(es1 ++ Seq(l1) ++ es2, l2)))
        case Block(e :: Nil, last) =>
          (e, Some(last))
        case Block(e :: es, last) =>
          (e, Some(Block(es, last)))
        case e =>
          (e, None)
      }

      var rest = tmpRest

      val res = current match {
        case ExArrayLiteral(tpe, args) =>
          FiniteArray(args.map(extractTree)).setType(ArrayType(extractType(tpe)))

        case ExCaseObject(sym) =>
          classesToClasses.get(sym) match {
            case Some(ccd: CaseClassDef) =>
              CaseClass(CaseClassType(ccd, Seq()), Seq())
            case _ =>
              unsupported(tr, "Unknown case object "+sym.name)
          }


        case ExParameterlessMethodCall(t,n) if extractTree(t).getType.isInstanceOf[CaseClassType] =>
          val selector = extractTree(t)
          val selType = selector.getType.asInstanceOf[CaseClassType]


          val fieldID = selType.fields.find(_.id.name == n.toString) match {
            case None =>
              unsupported(tr, "Invalid method or field invocation (not a case class arg?)")

            case Some(vd) =>
              vd.id
          }

          CaseClassSelector(selType, selector, fieldID)

        case ExTuple(tpes, exprs) =>
          val tupleExprs = exprs.map(e => extractTree(e))
          val tupleType = TupleType(tupleExprs.map(expr => expr.getType))
          Tuple(tupleExprs)

        case ExErrorExpression(str, tpe) =>
          Error(str).setType(extractType(tpe))

        case ExTupleExtract(tuple, index) =>
          val tupleExpr = extractTree(tuple)

          tupleExpr.getType match {
            case TupleType(tpes) if tpes.size >= index =>
              TupleSelect(tupleExpr, index)

            case _ =>
              unsupported(tr, "Invalid tupple access")
          }

        case ExValDef(vs, tpt, bdy) =>
          val binderTpe = extractType(tpt.tpe)
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = extractTree(bdy)

          if(valTree.getType.isInstanceOf[ArrayType]) {
            getOwner(valTree) match {
              case None =>
                owners += (newID -> Some(currentFunDef))
              case _ =>
                unsupported(tr, "Cannot alias array")
            }
          }

          val restTree = rest match {
            case Some(rst) => {
              varSubsts += vs -> (() => Variable(newID))
              val res = extractTree(rst)
              varSubsts -= vs
              res
            }
            case None => UnitLiteral
          }

          rest = None
          Let(newID, valTree, restTree)

        /**
         * XLang Extractors
         */

        case ExFunctionDef(symbol, tparams, params, ret, b) =>
          val funDef = extractFunSig(symbol, tparams, params, ret)
          defsToDefs += (symbol -> funDef)
          val oldMutableVarSubst = mutableVarSubsts.toMap //take an immutable snapshot of the map
          val oldCurrentFunDef = currentFunDef
          mutableVarSubsts.clear //reseting the visible mutable vars, we do not handle mutable variable closure in nested functions
          val funDefWithBody = extractFunDef(funDef, b)
          mutableVarSubsts ++= oldMutableVarSubst
          currentFunDef = oldCurrentFunDef
          val restTree = rest match {
            case Some(rst) => extractTree(rst)
            case None => UnitLiteral
          }
          defsToDefs -= symbol
          rest = None
          LetDef(funDefWithBody, restTree)

        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = extractType(tpt.tpe)
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = extractTree(bdy)
          mutableVarSubsts += (vs -> (() => Variable(newID)))

          if(valTree.getType.isInstanceOf[ArrayType]) {
            getOwner(valTree) match {
              case None =>
                owners += (newID -> Some(currentFunDef))
              case Some(_) =>
                unsupported(tr, "Cannot alias array")
            }
          }
          val restTree = rest match {
            case Some(rst) => {
              varSubsts += vs -> (() => Variable(newID))
              val res = extractTree(rst)
              varSubsts -= vs
              res
            }
            case None => UnitLiteral
          }

          rest = None

          LetVar(newID, valTree, restTree)
        }

        case ExAssign(sym, rhs) => mutableVarSubsts.get(sym) match {
          case Some(fun) =>
            val Variable(id) = fun()
            val rhsTree = extractTree(rhs)
            if(rhsTree.getType.isInstanceOf[ArrayType] && getOwner(rhsTree).isDefined) {
              unsupported(tr, "Cannot alias array")
            }
            Assignment(id, rhsTree)

          case None =>
            unsupported(tr, "Undeclared variable.")
        }

        case wh @ ExWhile(cond, body) =>
          val condTree = extractTree(cond)
          val bodyTree = extractTree(body)
          While(condTree, bodyTree)

        case wh @ ExWhileWithInvariant(cond, body, inv) =>
          val condTree = extractTree(cond)
          val bodyTree = extractTree(body)
          val invTree = extractTree(inv)

          val w = While(condTree, bodyTree)
          w.invariant = Some(invTree)
          w

        case epsi @ ExEpsilonExpression(tpe, varSym, predBody) =>
          val pstpe = extractType(tpe)
          val previousVarSubst: Option[Function0[LeonExpr]] = varSubsts.get(varSym) //save the previous in case of nested epsilon
          varSubsts += varSym -> (() => EpsilonVariable(epsi.pos).setType(pstpe))
          val c1 = extractTree(predBody)
          previousVarSubst match {
            case Some(f) => varSubsts += varSym -> f
            case None => varSubsts -= varSym
          }
          if(containsEpsilon(c1)) {
            unsupported(epsi, "Usage of nested epsilon is not allowed")
          }
          Epsilon(c1).setType(pstpe)

        case ExWaypointExpression(tpe, i, tree) =>
          val pstpe = extractType(tpe)
          val IntLiteral(ri) = extractTree(i)
          Waypoint(ri, extractTree(tree)).setType(pstpe)

        case update @ ExUpdate(lhs, index, newValue) =>
          val lhsRec = extractTree(lhs)
          lhsRec match {
            case Variable(_) =>
            case _ =>
              unsupported(tr, "Array update only works on variables")
          }

          getOwner(lhsRec) match {
            case Some(Some(fd)) if fd != currentFunDef =>
              unsupported(tr, "cannot update an array that is not defined locally")

            case Some(None) =>
              unsupported(tr, "cannot update an array that is not defined locally")

            case Some(_) =>

            case None => sys.error("This array: " + lhsRec + " should have had an owner")
          }

          val indexRec = extractTree(index)
          val newValueRec = extractTree(newValue)
          ArrayUpdate(lhsRec, indexRec, newValueRec)

        case ExInt32Literal(v) =>
          IntLiteral(v)

        case ExBooleanLiteral(v) =>
          BooleanLiteral(v)

        case ExUnitLiteral() =>
          UnitLiteral

        case ExLocally(body) =>
          extractTree(body)

        case ExTyped(e,tpt) =>
          // TODO: refine type here?
          extractTree(e)

        case ex @ ExIdentifier(sym,tpt) => varSubsts.get(sym) match {
          case Some(fun) => fun().setPos(ex.pos)
          case None => mutableVarSubsts.get(sym) match {
            case Some(fun) => fun().setPos(ex.pos)
            case None =>
              unsupported(tr, "Unidentified variable.")
          }
        }

        case chs @ ExChooseExpression(args, tpe, body, select) =>
          val cTpe  = extractType(tpe)

          val vars = args map { case (tpe, sym) =>
            val aTpe  = extractType(tpe)
            val newID = FreshIdentifier(sym.name.toString).setType(aTpe)
            owners += (newID -> None)
            varSubsts += sym -> (() => Variable(newID))
            newID
          }

          val cBody = extractTree(body)

          Choose(vars, cBody)

        case ExCaseClassConstruction(tpt, args) =>
          extractType(tpt.tpe) match {
            case cct: CaseClassType =>
              val nargs = args.map(extractTree(_))
              CaseClass(cct, nargs)

            case _ =>
              unsupported(tr, "Construction of a non-case class.")

          }

        case ExAnd(l, r)           => And(extractTree(l), extractTree(r))
        case ExOr(l, r)            => Or(extractTree(l), extractTree(r))
        case ExNot(e)              => Not(extractTree(e))
        case ExUMinus(e)           => UMinus(extractTree(e))
        case ExPlus(l, r)          => Plus(extractTree(l), extractTree(r))
        case ExMinus(l, r)         => Minus(extractTree(l), extractTree(r))
        case ExTimes(l, r)         => Times(extractTree(l), extractTree(r))
        case ExDiv(l, r)           => Division(extractTree(l), extractTree(r))
        case ExMod(l, r)           => Modulo(extractTree(l), extractTree(r))
        case ExNotEquals(l, r)     => Not(Equals(extractTree(l), extractTree(r)))
        case ExGreaterThan(l, r)   => GreaterThan(extractTree(l), extractTree(r))
        case ExGreaterEqThan(l, r) => GreaterEquals(extractTree(l), extractTree(r))
        case ExLessThan(l, r)      => LessThan(extractTree(l), extractTree(r))
        case ExLessEqThan(l, r)    => LessEquals(extractTree(l), extractTree(r))
        case ExEquals(l, r) =>
          val rl = extractTree(l)
          val rr = extractTree(r)

          (rl.getType, rr.getType) match {
            case (SetType(_), SetType(_)) =>
              SetEquals(rl, rr)

            case (BooleanType, BooleanType) =>
              Iff(rl, rr)

            case (rt, lt) if isSubtypeOf(rt, lt) || isSubtypeOf(lt, rt) =>
              Equals(rl, rr)

            case (rt, lt) =>
              unsupported(tr, "Invalid comparison: (_: "+rt+") == (_: "+lt+")")
          }

        case ExFiniteSet(tt, args)  =>
          val underlying = extractType(tt.tpe)
          FiniteSet(args.map(extractTree(_))).setType(SetType(underlying))

        case ExFiniteMultiset(tt, args) =>
          val underlying = extractType(tt.tpe)
          FiniteMultiset(args.map(extractTree(_))).setType(MultisetType(underlying))

        case ExEmptySet(tt) =>
          val underlying = extractType(tt.tpe)
          FiniteSet(Seq()).setType(SetType(underlying))

        case ExEmptyMultiset(tt) =>
          val underlying = extractType(tt.tpe)
          EmptyMultiset(underlying).setType(MultisetType(underlying))

        case ExEmptyMap(ft, tt) =>
          val fromUnderlying = extractType(ft.tpe)
          val toUnderlying   = extractType(tt.tpe)
          val tpe = MapType(fromUnderlying, toUnderlying)

          FiniteMap(Seq()).setType(tpe)

        case ExLiteralMap(ft, tt, elems) =>
          val fromUnderlying = extractType(ft.tpe)
          val toUnderlying   = extractType(tt.tpe)
          val tpe = MapType(fromUnderlying, toUnderlying)

          val singletons: Seq[(LeonExpr, LeonExpr)] = elems.collect {
            case ExTuple(tpes, trees) if (trees.size == 2) =>
              (extractTree(trees(0)), extractTree(trees(1)))
          }

          if (singletons.size != elems.size) {
            unsupported(tr, "Some map elements could not be extracted as Tuple2")
          }

          FiniteMap(singletons).setType(tpe)

        case ExSetMin(t) =>
          val set = extractTree(t)
          set.getType match {
            case SetType(base) =>
              SetMin(set).setType(base)

            case _ =>
              unsupported(t, "Min should be computer on a set.")
          }

        case ExSetMax(t) =>
          val set = extractTree(t)
          set.getType match {
            case SetType(base) =>
              SetMax(set).setType(base)

            case _ =>
              unsupported(t, "Max should be computer on a set.")
          }

        case ExUnion(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)

          (rl.getType, rr.getType) match {
            case (SetType(b1), SetType(b2)) if b1 == b2 =>
              SetUnion(rl, rr).setType(SetType(b1))

            case (MultisetType(b1), MultisetType(b2)) if b1 == b2 =>
              MultisetUnion(rl, rr).setType(SetType(b1))

            case (lt, rt) =>
              unsupported(tr, "Unsupported union between "+lt+" and "+rt)
          }

        case ExIntersection(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)

          (rl.getType, rr.getType) match {
            case (SetType(b1), SetType(b2)) if b1 == b2 =>
              SetIntersection(rl, rr).setType(SetType(b1))

            case (MultisetType(b1), MultisetType(b2)) if b1 == b2 =>
              MultisetIntersection(rl, rr).setType(SetType(b1))

            case (lt, rt) =>
              unsupported(tr, "Unsupported intersection between "+lt+" and "+rt)
          }

        case ExSetContains(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)

          (rl.getType, rr.getType) match {
            case (SetType(base), elem) if isSubtypeOf(elem, base) =>
              ElementOfSet(rr, rl)

            case (lt, rt) =>
              unsupported(tr, "Invalid "+lt+".contains("+rt+")")
          }

        case ExSetSubset(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)

          (rl.getType, rr.getType) match {
            case (SetType(base1), SetType(base2)) if base2 == base1 =>
              SubsetOf(rl, rr)

            case (lt, rt) =>
              unsupported(tr, "Invalid "+lt+" isSubsetOf "+rt+"")
          }

        case ExSetMinus(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)

          (rl.getType, rr.getType) match {
            case (SetType(base1), SetType(base2)) if base2 == base1 =>
              SetDifference(rl, rr).setType(SetType(base1))

            case (MultisetType(base1), MultisetType(base2)) if base2 == base1 =>
              MultisetDifference(rl, rr).setType(MultisetType(base1))

            case (lt, rt) =>
              unsupported(tr, "Invalid "+lt+" -- "+rt+"")
          }

        case ExSetCard(t) =>
          val rt = extractTree(t)
          rt.getType match {
            case SetType(_) =>
              SetCardinality(rt)

            case MultisetType(_) =>
              MultisetCardinality(rt)

            case _ =>
              unsupported(tr, "Cardinality of non set/multiset expressions.")
          }

        case ExMultisetToSet(t) =>
          val rt = extractTree(t)

          rt.getType match {
            case MultisetType(u) =>
              MultisetToSet(rt).setType(SetType(u))

            case _ =>
              unsupported(tr, "toSet can only be applied to multisets.")
          }

        case up @ ExUpdated(m, f, t) =>
          val rm = extractTree(m)
          val rf = extractTree(f)
          val rt = extractTree(t)

          rm.getType match {
            case t @ MapType(ft, tt) =>
              MapUnion(rm, FiniteMap(Seq((rf, rt))).setType(t)).setType(t)

            case t @ ArrayType(bt) =>
              ArrayUpdated(rm, rf, rt).setType(t)

            case _ =>
              unsupported(tr, "updated can only be applied to maps.")
          }

        case ExMapIsDefinedAt(m,k) =>
          val rm = extractTree(m)
          val rk = extractTree(k)
          MapIsDefinedAt(rm, rk)

        case ExPlusPlusPlus(t1,t2) =>
          val rl = extractTree(t1)
          val rr = extractTree(t2)
          MultisetPlus(rl, rr).setType(rl.getType)

        case app @ ExApply(lhs,args) =>
          val rlhs = extractTree(lhs)
          val rargs = args map extractTree

          rlhs.getType match {
            case MapType(_,tt) =>
              assert(rargs.size == 1)
              MapGet(rlhs, rargs.head).setType(tt)

            case ArrayType(bt) =>
              assert(rargs.size == 1)
              ArraySelect(rlhs, rargs.head).setType(bt)

            case _ =>
              unsupported(tr, "apply on unexpected type")
          }

        case ExArrayLength(t) =>
          val rt = extractTree(t)
          ArrayLength(rt)

        case ExArrayClone(t) =>
          val rt = extractTree(t)
          ArrayClone(rt)

        case ExArrayFill(baseType, length, defaultValue) =>
          val underlying = extractType(baseType.tpe)
          val lengthRec = extractTree(length)
          val defaultValueRec = extractTree(defaultValue)
          ArrayFill(lengthRec, defaultValueRec).setType(ArrayType(underlying))

        case ExIfThenElse(t1,t2,t3) =>
          val r1 = extractTree(t1)
          if(containsLetDef(r1)) {
            unsupported(t1, "Condition of if-then-else expression should not contain nested function definition")
          }
          val r2 = extractTree(t2)
          val r3 = extractTree(t3)
          val lub = leastUpperBound(r2.getType, r3.getType)
          lub match {
            case Some(lub) =>
              IfExpr(r1, r2, r3).setType(lub)

            case None =>
              unsupported(tr, "Both branches of ifthenelse have incompatible types")
          }

        case ExIsInstanceOf(tt, cc) => {
          val ccRec = extractTree(cc)
          val checkType = extractType(tt.tpe)
          checkType match {
            case cct @ CaseClassType(ccd, tps) => {
              val rootType: LeonClassDef  = if(ccd.parent != None) ccd.parent.get.classDef else ccd

              if(!ccRec.getType.isInstanceOf[ClassType]) {
                reporter.error(tr.pos, "isInstanceOf can only be used with a case class")
                throw ImpureCodeEncounteredException(tr)
              } else {
                val testedExprType = ccRec.getType.asInstanceOf[ClassType].classDef
                val testedExprRootType: LeonClassDef = if(testedExprType.parent != None) testedExprType.parent.get.classDef else testedExprType

                if(rootType != testedExprRootType) {
                  reporter.error(tr.pos, "isInstanceOf can only be used with compatible case classes")
                  throw ImpureCodeEncounteredException(tr)
                } else {
                  CaseClassInstanceOf(cct, ccRec)
                }
              }
            }
            case _ => {
              reporter.error(tr.pos, "isInstanceOf can only be used with a case class")
              throw ImpureCodeEncounteredException(tr)
            }
          }
        }

        case lc @ ExLocalCall(sym, tps, ar) =>
          if (!defsToDefs.contains(sym)) {
            reporter.error(lc.pos, "Invoking an invalid function.")
            throw ImpureCodeEncounteredException(tr)
          }

          val fd = defsToDefs(sym)

          val newTps = tps.map(t => extractType(t.tpe))

          FunctionInvocation(fd.typed(newTps), ar.map(extractTree(_))).setType(fd.returnType)

        case pm @ ExPatternMatching(sel, cses) =>
          val rs = extractTree(sel)
          val rc = cses.map(extractMatchCase(_))
          val rt: LeonType = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_).get)
          MatchExpr(rs, rc).setType(rt)


        // default behaviour is to complain :)
        case _ =>
          unsupported(tr, "Could not extract as PureScala")
      }

      res.setPos(current.pos)

      rest match {
        case Some(r) =>
          LeonBlock(Seq(res), extractTree(r))
        case None =>
          res
      }
    }

    private def extractType(tpt: Type)(implicit dctx: DefContext): LeonType = tpt match {
      case tpe if tpe == IntClass.tpe =>
        Int32Type

      case tpe if tpe == BooleanClass.tpe =>
        BooleanType

      case tpe if tpe == UnitClass.tpe =>
        UnitType

      case tpe if tpe == NothingClass.tpe =>
        BottomType

      case TypeRef(_, sym, btt :: Nil) if isSetTraitSym(sym) =>
        SetType(extractType(btt))

      case TypeRef(_, sym, btt :: Nil) if isMultisetTraitSym(sym) =>
        MultisetType(extractType(btt))

      case TypeRef(_, sym, List(ftt,ttt)) if isMapTraitSym(sym) =>
        MapType(extractType(ftt), extractType(ttt))

      case TypeRef(_, sym, List(t1,t2)) if isTuple2(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2)))

      case TypeRef(_, sym, List(t1,t2,t3)) if isTuple3(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3)))

      case TypeRef(_, sym, List(t1,t2,t3,t4)) if isTuple4(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4)))

      case TypeRef(_, sym, List(t1,t2,t3,t4,t5)) if isTuple5(sym) =>
        TupleType(Seq(extractType(t1),extractType(t2),extractType(t3),extractType(t4),extractType(t5)))

      case TypeRef(_, sym, btt :: Nil) if isArrayClassSym(sym) =>
        ArrayType(extractType(btt))

      case TypeRef(_, sym, tps) if classesToClasses contains sym =>
        val leontps = tps.map(extractType)

        classDefToClassType(classesToClasses(sym), leontps)

      case TypeRef(_, sym, Nil) =>
        if(dctx.tparams contains sym) {
          dctx.tparams(sym)
        } else {
          println(sym.id)
          println(classesToClasses.map{ case (sym, cd) => sym.id+" -> "+cd.id }.mkString("\n"))
          unsupported("Type parameter "+tpt+" is unknown (Known: "+dctx.tparams.values.mkString(", ")+")")
        }

      case SingleType(_, sym) if classesToClasses contains sym.moduleClass=>
        classDefToClassType(classesToClasses(sym.moduleClass), Nil)

      case _ =>
        unsupported("Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
    }

    private def getReturnedExpr(expr: LeonExpr): Seq[LeonExpr] = expr match {
      case Let(_, _, rest) => getReturnedExpr(rest)
      case LetVar(_, _, rest) => getReturnedExpr(rest)
      case LeonBlock(_, rest) => getReturnedExpr(rest)
      case IfExpr(_, thenn, elze) => getReturnedExpr(thenn) ++ getReturnedExpr(elze)
      case MatchExpr(_, cses) => cses.flatMap{
        case SimpleCase(_, rhs) => getReturnedExpr(rhs)
        case GuardedCase(_, _, rhs) => getReturnedExpr(rhs)
      }
      case _ => Seq(expr)
    }

    def getOwner(exprs: Seq[LeonExpr]): Option[Option[FunDef]] = {
      val exprOwners: Seq[Option[Option[FunDef]]] = exprs.map {
        case Variable(id) =>
          owners.get(id)
        case _ =>
          None
      }

      if(exprOwners.exists(_ == None))
        None
      else if(exprOwners.exists(_ == Some(None)))
        Some(None)
      else if(exprOwners.exists(o1 => exprOwners.exists(o2 => o1 != o2)))
        Some(None)
      else
        exprOwners(0)
    }

    def getOwner(expr: LeonExpr): Option[Option[FunDef]] = getOwner(getReturnedExpr(expr))

    def extractProgram: Option[Program] = {
      val topLevelObjDef = extractTopLevelDef

      val programName: Identifier = unit.body match {
        case PackageDef(name, _) => FreshIdentifier(name.toString)
        case _                   => FreshIdentifier("<program>")
      }

      topLevelObjDef.map(obj => Program(programName, obj))
    }
  }

  def containsLetDef(expr: LeonExpr): Boolean = {
    exists { _ match {
      case (l: LetDef) => true
      case _ => false
    }}(expr)
  }
}
