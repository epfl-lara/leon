/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.tools.nsc._
import scala.reflect.internal.util._
import scala.tools.nsc.plugins._

import scala.language.implicitConversions

import purescala._
import purescala.Definitions.{ClassDef => LeonClassDef, ModuleDef => LeonModuleDef, ValDef => LeonValDef, _}
import purescala.Trees.{Expr => LeonExpr, This => LeonThis, _}
import purescala.TypeTrees.{TypeTree => LeonType, _}
import purescala.Common._
import purescala.Extractors.IsTyped
import purescala.TreeOps._
import purescala.TypeTreeOps._
import xlang.Trees.{Block => LeonBlock, _}
import xlang.TreeOps._

import utils.{DefinedPosition, Position => LeonPosition, OffsetPosition => LeonOffsetPosition, RangePosition => LeonRangePosition}

trait CodeExtraction extends ASTExtractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import ExtractorHelpers._
  import scala.collection.immutable.Set

  def annotationsOf(s: Symbol): Set[String] = {
    (for(a <- s.annotations) yield {
      val name = a.atp.safeToString
      if (name startsWith "leon.annotation.") {
        Some(name.split("\\.", 3)(2))
      } else {
        None
      }
    }).flatten.toSet
  }

  implicit def scalaPosToLeonPos(p: global.Position): LeonPosition = {
    if (p == NoPosition) {
      leon.utils.NoPosition
    } else if (p.isRange) {
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

  def leonPosToScalaPos(sf: SourceFile, p: LeonPosition): global.Position = {
    p match {
      case dp: DefinedPosition =>
        new OffsetPosition(sf, dp.focusBegin.point)

      case _ =>
        NoPosition

    }
  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(pos: Position, msg: String, ot: Option[Tree]) extends Exception(msg) {
    def emit() {
      val debugInfo = if (ctx.settings.debugSections contains utils.DebugSectionTrees) {
        ot.map { t => 
          val strWr = new java.io.StringWriter()
          new global.TreePrinter(new java.io.PrintWriter(strWr)).printTree(t)
          " (Tree: "+strWr.toString+" ; Class: "+t.getClass+")"
        }.getOrElse("")
      } else {
        ""
      }

      if (ctx.settings.strictCompilation) {
        reporter.error(pos, msg + debugInfo)
      } else {
        reporter.warning(pos, msg + debugInfo)
      }
    }
  }

  def outOfSubsetError(pos: Position, msg: String) = {
    throw new ImpureCodeEncounteredException(pos, msg, None)
  }

  def outOfSubsetError(t: Tree, msg: String) = {
    throw new ImpureCodeEncounteredException(t.pos, msg, Some(t))
  }

  class Extraction(units: List[CompilationUnit]) {
    private var currentFunDef: FunDef = null

    //This is a bit missleading, if an expr is not mapped then it has no owner, if it is mapped to None it means
    //that it can have any owner
    private var owners: Map[Identifier, Option[FunDef]] = Map() 


    def toPureScala(tree: Tree)(implicit dctx: DefContext): Option[LeonExpr] = {
      try {
        Some(extractTree(tree))
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.emit()
          None
      }
    }

    // This one never fails, on error, it returns Untyped
    def toPureScalaType(tpt: Type)(implicit dctx: DefContext): LeonType = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.emit()
          Untyped
      }
    }

    case class DefContext(
        tparams: Map[Symbol, TypeParameter] = Map(),
        vars: Map[Symbol, () => LeonExpr] = Map(),
        mutableVars: Map[Symbol, () => LeonExpr] = Map(),
        isProxy: Boolean = false
      ) {

      def union(that: DefContext) = {
        copy(this.tparams ++ that.tparams,
             this.vars ++ that.vars,
             this.mutableVars ++ that.mutableVars,
             this.isProxy || that.isProxy)
      }

      def isVariable(s: Symbol) = (vars contains s) || (mutableVars contains s)

      def withNewVars(nvars: Traversable[(Symbol, () => LeonExpr)]) = {
        copy(vars = vars ++ nvars)
      }

      def withNewVar(nvar: (Symbol, () => LeonExpr)) = {
        copy(vars = vars + nvar)
      }

      def withNewMutableVar(nvar: (Symbol, () => LeonExpr)) = {
        copy(mutableVars = mutableVars + nvar)
      }
    }

    def extractModules: List[LeonModuleDef] = {
      try {
        val templates: List[(String, List[Tree])] = units.reverse.flatMap { u => u.body match {
          case PackageDef(name, lst) =>
            var standaloneDefs = List[Tree]()

            val modules: List[(String, List[Tree])] = lst.flatMap { _ match {
              case od @ ExObjectDef(_, _) if annotationsOf(od.symbol) contains "ignore" =>
                None

              case ExObjectDef(n, templ) =>
                Some((n.toString, templ.body))

              case d @ ExAbstractClass(_, _, _) =>
                standaloneDefs ::= d
                None

              case d @ ExCaseClass(_, _, _, _) =>
                standaloneDefs ::= d
                None

              case d @ ExCaseClassSyntheticJunk() =>
                None

              case other =>
                outOfSubsetError(other, "Expected: top-level object/class.")
                None
            }}.toList

            val extraModules: List[(String, List[Tree])] = if (standaloneDefs.isEmpty) {
              Nil
            } else {
              List(("standalone", standaloneDefs.reverse))
            }

            modules ++ extraModules
        }}

        // Phase 1, we detect classes/types
        templates.foreach{ case (name, templ) => collectClassSymbols(templ) }

        // Phase 2, we collect functions signatures
        templates.foreach{ case (name, templ) => collectFunSigs(templ) }

        // Phase 3, we collect classes/types' definitions
        templates.foreach{ case (name, templ) => extractClassDefs(templ) }

        // Phase 4, we collect methods' definitions
        templates.foreach{ case (name, templ) => extractMethodDefs(templ) }

        // Phase 5, we collect function definitions
        templates.foreach{ case (name, templ) => extractFunDefs(templ) }

        // Phase 6, we create modules and extract bodies
        templates.map{ case (name, templ) => extractObjectDef(name, templ) }
      } catch {
        case icee: ImpureCodeEncounteredException =>
          icee.emit()
          Nil
      }

    }

    private var seenClasses = Map[Symbol, (Seq[(String, Tree)], Template)]()
    private var classesToClasses  = Map[Symbol, LeonClassDef]()

    private def collectClassSymbols(defs: List[Tree]) {
      // We collect all defined classes
      for (t <- defs) t match {
        case ExAbstractClass(o2, sym, tmpl) =>
          seenClasses += sym -> ((Nil, tmpl))

        case ExCaseClass(o2, sym, args, tmpl) =>
          seenClasses += sym -> ((args, tmpl))

        case _ =>
      }
    }

    private def extractClassDefs(defs: List[Tree]) {
      // We collect all defined classes
      for (t <- defs) t match {
        case ExAbstractClass(o2, sym, _) =>
          getClassDef(sym, NoPosition)

        case ExCaseClass(o2, sym, args, _) =>
          getClassDef(sym, NoPosition)

        case _ =>
      }
    }

    def getClassDef(sym: Symbol, pos: Position): LeonClassDef = {
      classesToClasses.get(sym) match {
        case Some(cd) => cd
        case None =>
          if (seenClasses contains sym) {
            val (args, tmpl) = seenClasses(sym)

            extractClassDef(sym, args, tmpl)
          } else {
            outOfSubsetError(pos, "Class "+sym.name+" not defined?")
          }
      }
    }

    def getFunDef(sym: Symbol, pos: Position): FunDef = {
      defsToDefs.get(sym) match {
        case Some(fd) => fd
        case None =>
          outOfSubsetError(pos, "Function "+sym.name+" not properly defined?")
      }
    }

    private var isMethod = Set[Symbol]()
    private var methodToClass = Map[FunDef, LeonClassDef]()

    def extractClassDef(sym: Symbol, args: Seq[(String, Tree)], tmpl: Template): LeonClassDef = {
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
        case Some(TypeRef(_, parentSym, tps)) if seenClasses contains parentSym =>
          getClassDef(parentSym, sym.pos) match {
            case acd: AbstractClassDef =>
              val newTps = tps.map(extractType(_)(defCtx))
              Some(AbstractClassType(acd, newTps))

            case cd =>
              outOfSubsetError(sym.pos, "Class "+id+" cannot extend "+cd.id)
              None
          }

        case p =>
          None
      }

      val cd = if (sym.isAbstractClass) {
        val acd = AbstractClassDef(id, tparams, parent).setPos(sym.pos)

        classesToClasses += sym -> acd

        acd
      } else {
        val ccd = CaseClassDef(id, tparams, parent, sym.isModuleClass).setPos(sym.pos)

        parent.foreach(_.classDef.registerChildren(ccd))

        classesToClasses += sym -> ccd

        val fields = args.map { case (name, t) =>
          val tpe = toPureScalaType(t.tpe)(defCtx)
          LeonValDef(FreshIdentifier(name).setType(tpe).setPos(t.pos), tpe).setPos(t.pos)
        }

        ccd.setFields(fields)

        // Validates type parameters
        parent match {
          case Some(pct) =>
            if(pct.classDef.tparams.size == tparams.size) {
              val pcd = pct.classDef
              val ptps = pcd.tparams.map(_.tp)

              val targetType = AbstractClassType(pcd, ptps)
              val fromChild = CaseClassType(ccd, ptps).parent.get

              if (fromChild != targetType) {
                outOfSubsetError(sym.pos, "Child type should form a simple bijection with parent class type (e.g. C[T1,T2] extends P[T1,T2])")
              }

            } else {
              outOfSubsetError(sym.pos, "Child classes should have the same number of type parameters as their parent")
            }
          case _ =>
        }

        ccd
      }

      // We collect the methods
      for (d <- tmpl.body) d match {
        case t @ ExFunctionDef(fsym, _, _, _, _) if !fsym.isSynthetic && !fsym.isAccessor =>
          if (parent.isDefined) {
            outOfSubsetError(t, "Only hierarchy roots can define methods")
          }
          val fd = defineFunDef(fsym)(defCtx)

          isMethod += fsym
          methodToClass += fd -> cd

          cd.registerMethod(fd)

        case _ =>
      }

      cd
    }

    private var defsToDefs        = Map[Symbol, FunDef]()

    private def defineFunDef(sym: Symbol)(implicit dctx: DefContext): FunDef = {
      // Type params of the function itself
      val tparams = extractTypeParams(sym.typeParams.map(_.tpe))

      val isProxy = annotationsOf(sym) contains "proxy"

      val nctx = dctx.copy(tparams = dctx.tparams ++ tparams.toMap, isProxy = isProxy)

      val newParams = sym.info.paramss.flatten.map{ sym =>
        val ptpe = toPureScalaType(sym.tpe)(nctx)
        val newID = FreshIdentifier(sym.name.toString).setType(ptpe).setPos(sym.pos)
        owners += (newID -> None)
        LeonValDef(newID, ptpe).setPos(sym.pos)
      }

      val tparamsDef = tparams.map(t => TypeParameterDef(t._2))

      val returnType = toPureScalaType(sym.info.finalResultType)(nctx)

      val name = sym.name.toString

      val fd = new FunDef(FreshIdentifier(name).setPos(sym.pos), tparamsDef, returnType, newParams)

      fd.setPos(sym.pos)

      fd.addAnnotation(annotationsOf(sym).toSeq : _*)

      defsToDefs += sym -> fd

      fd
    }

    private def collectFunSigs(defs: List[Tree]) = {
      // We collect defined function bodies
      for (d <- defs) d match {
        case ExMainFunctionDef() =>
          // Ignoring...

        case ExFunctionDef(sym, _, _, _, _) =>
          defineFunDef(sym)(DefContext())

        case _ =>
      }
    }

    private def extractMethodDefs(defs: List[Tree]) = {
      // We collect defined function bodies
      def extractFromClass(csym: Symbol, tmpl: Template) {
        val cd = classesToClasses(csym)

        val ctparams = csym.tpe match {
          case TypeRef(_, _, tps) =>
            extractTypeParams(tps).map(_._1)
          case _ =>
            Nil
        }

        val ctparamsMap = ctparams zip cd.tparams.map(_.tp)

        for (d <- tmpl.body) d match {
          case ExFunctionDef(sym, tparams, params, _, body) if !sym.isSynthetic && !sym.isAccessor =>
            val fd = defsToDefs(sym)

            val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap ++ ctparamsMap

            if(body != EmptyTree) {
              extractFunBody(fd, params, body)(DefContext(tparamsMap))
            }

          case _ =>

        }
      }
      for (d <- defs) d match {
        case ExAbstractClass(_, csym, tmpl) =>
          extractFromClass(csym, tmpl)

        case ExCaseClass(_, csym, _, tmpl) =>
          extractFromClass(csym, tmpl)

        case _ =>
      }
    }

    private def extractFunDefs(defs: List[Tree]) = {
      // We collect defined function bodies
      for (d <- defs) d match {
        case ExMainFunctionDef() =>
          // Ignoring...

        case ExFunctionDef(sym, tparams, params, _, body) =>
          val fd = defsToDefs(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          extractFunBody(fd, params, body)(DefContext(tparamsMap))

        case _ =>
      }
    }

    private def extractTypeParams(tps: Seq[Type]): Seq[(Symbol, TypeParameter)] = {
      tps.flatMap {
        case TypeRef(_, sym, Nil) =>
          Some(sym -> TypeParameter(FreshIdentifier(sym.name.toString)))
        case t =>
          outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
          None
      }
    }

    private def extractObjectDef(nameStr: String, defs: List[Tree]): LeonModuleDef = {

      val newDefs = defs.flatMap{ t => t match {
        case ExAbstractClass(o2, sym, _) =>
          Some(classesToClasses(sym))

        case ExCaseClass(o2, sym, args, _) =>
          Some(classesToClasses(sym))

        case ExMainFunctionDef() =>
          // Ignoring...
          None

        case ExFunctionDef(sym, tparams, params, _, body) =>
          Some(defsToDefs(sym))

        case _ =>
          None
      }}

      // We check nothing else is polluting the object
      for (t <- defs) t match {
        case ExCaseClassSyntheticJunk() =>
        case ExAbstractClass(_,_,_) =>
        case ExCaseClass(_,_,_,_) =>
        case ExConstructorDef() =>
        case ExMainFunctionDef() =>
        case ExFunctionDef(_, _, _, _, _) =>
        case defn if annotationsOf(defn.symbol) contains "ignore" =>
        case tree =>
          outOfSubsetError(tree, "Don't know what to do with this. Not purescala?");
      }

      new LeonModuleDef(FreshIdentifier(nameStr), newDefs)
    }


    private def extractFunBody(funDef: FunDef, params: Seq[ValDef], body: Tree)(implicit dctx: DefContext): FunDef = {
      currentFunDef = funDef

      val newVars = for ((s, vd) <- params zip funDef.params) yield {
        s.symbol -> (() => Variable(vd.id))
      }


      val fctx = dctx.withNewVars(newVars)


      val (body2, ensuring) = body match {
        case ExEnsuredExpression(body2, resSym, contract) =>
          val resId = FreshIdentifier(resSym.name.toString).setType(funDef.returnType).setPos(resSym.pos)
          val post = toPureScala(contract)(fctx.withNewVar(resSym -> (() => Variable(resId)))).map( r => (resId, r))

          (body2, post)

        case t @ ExHoldsExpression(body2) =>
          val resId = FreshIdentifier("holds").setType(BooleanType).setPos(body.pos)
          (body2, Some((resId, Variable(resId).setPos(body.pos))))

        case _ =>
          (body, None)
      }

      val (body3, require) = body2 match {
        case ExRequiredExpression(body3, contract) =>
          (body3, toPureScala(contract)(fctx))

        case _ =>
          (body2, None)
      }

      val finalBody = try {
        Some(flattenBlocks(extractTree(body3)(fctx)) match {
          case e if e.getType.isInstanceOf[ArrayType] =>
            getOwner(e) match {
              case Some(Some(fd)) if fd == funDef =>
                e

              case None =>
                e

              case _ =>
                outOfSubsetError(body3, "Function cannot return an array that is not locally defined")
            }
          case e =>
            e
        })
      } catch {
        case e: ImpureCodeEncounteredException =>
        if (funDef.annotations contains "proxy") {
          // We actually expect errors, no point reporting
        } else {
          e.emit()
          val pos = if (body.pos == NoPosition) NoPosition else leonPosToScalaPos(body.pos.source, funDef.getPos)
          if (ctx.settings.strictCompilation) {
            reporter.error(pos, "Function "+funDef.id.name+" could not be extracted. (Forgot @proxy ?)")
          } else {
            reporter.warning(pos, "Function "+funDef.id.name+" is not fully unavailable to Leon.")
          }
        }

        funDef.addAnnotation("abstract")
        None
      }

      val finalRequire = require.filter{ e =>
        if(containsLetDef(e)) {
          reporter.warning(body3.pos, "Function precondtion should not contain nested function definition, ignoring.")
          false
        } else {
          true
        }
      }

      val finalEnsuring = ensuring.filter{ case (id, e) =>
        if(containsLetDef(e)) {
          reporter.warning(body3.pos, "Function postcondition should not contain nested function definition, ignoring.")
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

    private def extractPattern(p: Tree, binder: Option[Identifier] = None)(implicit dctx: DefContext): (Pattern, DefContext) = p match {
      case b @ Bind(name, t @ Typed(pat, tpe)) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(tpe.tpe)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => Variable(newID)))
        extractPattern(t, Some(newID))(pctx)

      case b @ Bind(name, pat) =>
        val newID = FreshIdentifier(name.toString).setType(extractType(b.symbol.tpe)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => Variable(newID)))
        extractPattern(pat, Some(newID))(pctx)

      case t @ Typed(Ident(nme.WILDCARD), tpt) =>
        extractType(tpt.tpe) match {
          case ct: ClassType =>
            (InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

          case lt =>
            outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
        }

      case Ident(nme.WILDCARD) =>
        (WildcardPattern(binder).setPos(p.pos), dctx)

      case s @ Select(_, b) if s.tpe.typeSymbol.isCase  =>
        // case Obj =>
        extractType(s.tpe) match {
          case ct: CaseClassType =>
            assert(ct.classDef.fields.size == 0)
            (CaseClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
          case _ =>
            outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>

        extractType(a.tpe) match {
          case ct: CaseClassType =>
            assert(args.size == ct.classDef.fields.size)
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip

            val nctx = subDctx.foldLeft(dctx)(_ union _)

            (CaseClassPattern(binder, ct, subPatterns).setPos(p.pos), nctx)
          case TupleType(argsTpes) =>
            val (subPatterns, subDctx) = args.map(extractPattern(_)).unzip

            val nctx = subDctx.foldLeft(dctx)(_ union _)

            (TuplePattern(binder, subPatterns).setPos(p.pos), nctx)
          case _ =>
            outOfSubsetError(a, "Invalid type "+a.tpe+" for .isInstanceOf")
        }

      case _ =>
        outOfSubsetError(p, "Unsupported pattern: "+p.getClass)
    }

    private def extractMatchCase(cd: CaseDef)(implicit dctx: DefContext): MatchCase = {
      val (recPattern, ndctx) = extractPattern(cd.pat)
      val recBody             = extractTree(cd.body)(ndctx)

      if(cd.guard == EmptyTree) {
        SimpleCase(recPattern, recBody).setPos(cd.pos)
      } else {
        val recGuard = extractTree(cd.guard)(ndctx)

        if(isXLang(recGuard)) {
          outOfSubsetError(cd.guard.pos, "Guard expression must be pure") 
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
          getClassDef(sym, current.pos) match {
            case ccd: CaseClassDef =>
              CaseClass(CaseClassType(ccd, Seq()), Seq())
            case _ =>
              outOfSubsetError(current, "Unknown case object "+sym.name)
          }

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
              outOfSubsetError(current, "Invalid tupple access")
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
                outOfSubsetError(tr, "Cannot alias array")
            }
          }

          val restTree = rest match {
            case Some(rst) => {
              val nctx = dctx.withNewVar(vs -> (() => Variable(newID)))
              extractTree(rst)(nctx)
            }
            case None => UnitLiteral()
          }

          rest = None
          Let(newID, valTree, restTree)


        case d @ ExFunctionDef(sym, tparams, params, ret, b) =>
          val fd = defineFunDef(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          fd.addAnnotation(annotationsOf(d.symbol).toSeq : _*)

          val newDctx = dctx.copy(tparams = dctx.tparams ++ tparamsMap)

          val oldCurrentFunDef = currentFunDef

          val funDefWithBody = extractFunBody(fd, params, b)(newDctx.copy(mutableVars = Map()))

          currentFunDef = oldCurrentFunDef

          val restTree = rest match {
            case Some(rst) => extractTree(rst)
            case None => UnitLiteral()
          }
          rest = None
          LetDef(funDefWithBody, restTree)

        /**
         * XLang Extractors
         */

        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = extractType(tpt.tpe)
          val newID = FreshIdentifier(vs.name.toString).setType(binderTpe)
          val valTree = extractTree(bdy)

          if(valTree.getType.isInstanceOf[ArrayType]) {
            getOwner(valTree) match {
              case None =>
                owners += (newID -> Some(currentFunDef))
              case Some(_) =>
                outOfSubsetError(tr, "Cannot alias array")
            }
          }

          val restTree = rest match {
            case Some(rst) => {
              val nv = vs -> (() => Variable(newID))
              val nctx = dctx.withNewVar(nv).withNewMutableVar(nv)
              extractTree(rst)(nctx)
            }
            case None => UnitLiteral()
          }

          rest = None

          LetVar(newID, valTree, restTree)
        }

        case ExAssign(sym, rhs) => dctx.mutableVars.get(sym) match {
          case Some(fun) =>
            val Variable(id) = fun()
            val rhsTree = extractTree(rhs)
            if(rhsTree.getType.isInstanceOf[ArrayType] && getOwner(rhsTree).isDefined) {
              outOfSubsetError(tr, "Cannot alias array")
            }
            Assignment(id, rhsTree)

          case None =>
            outOfSubsetError(tr, "Undeclared variable.")
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
          val nctx = dctx.withNewVar(varSym -> (() => EpsilonVariable(epsi.pos).setType(pstpe)))
          val c1 = extractTree(predBody)(nctx)
          if(containsEpsilon(c1)) {
            outOfSubsetError(epsi, "Usage of nested epsilon is not allowed")
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
              outOfSubsetError(tr, "Array update only works on variables")
          }

          getOwner(lhsRec) match {
            case Some(Some(fd)) if fd != currentFunDef =>
              outOfSubsetError(tr, "cannot update an array that is not defined locally")

            case Some(None) =>
              outOfSubsetError(tr, "cannot update an array that is not defined locally")

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
          UnitLiteral()

        case ExLocally(body) =>
          extractTree(body)

        case ExTyped(e,tpt) =>
          // TODO: refine type here?
          extractTree(e)

        case ex @ ExIdentifier(sym, tpt) if dctx.isVariable(sym) =>
          dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
            case Some(builder) =>
              builder().setPos(ex.pos)
            case None =>
              outOfSubsetError(tr, "Unidentified variable "+sym+" "+sym.id+".")
          }

        case chs @ ExChooseExpression(args, tpe, body, select) =>
          val cTpe  = extractType(tpe)

          val vars = args map { case (tpe, sym) =>
            val aTpe  = extractType(tpe)
            val newID = FreshIdentifier(sym.name.toString).setType(aTpe)
            owners += (newID -> None)
            newID
          }

          val newVars = (args zip vars).map {
            case ((_, sym), id) =>
              sym -> (() => Variable(id))
          }

          val cBody = extractTree(body)(dctx.withNewVars(newVars))

          Choose(vars, cBody)

        case ExCaseClassConstruction(tpt, args) =>
          extractType(tpt.tpe) match {
            case cct: CaseClassType =>
              val nargs = args.map(extractTree(_))
              CaseClass(cct, nargs)

            case _ =>
              outOfSubsetError(tr, "Construction of a non-case class.")

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
              outOfSubsetError(tr, "Invalid comparison: (_: "+rt+") == (_: "+lt+")")
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
            outOfSubsetError(tr, "Some map elements could not be extracted as Tuple2")
          }

          FiniteMap(singletons).setType(tpe)

        case ExArrayFill(baseType, length, defaultValue) =>
          val underlying = extractType(baseType.tpe)
          val lengthRec = extractTree(length)
          val defaultValueRec = extractTree(defaultValue)
          ArrayFill(lengthRec, defaultValueRec).setType(ArrayType(underlying))

        case ExIfThenElse(t1,t2,t3) =>
          val r1 = extractTree(t1)
          if(containsLetDef(r1)) {
            outOfSubsetError(t1, "Condition of if-then-else expression should not contain nested function definition")
          }
          val r2 = extractTree(t2)
          val r3 = extractTree(t3)
          val lub = leastUpperBound(r2.getType, r3.getType)
          lub match {
            case Some(lub) =>
              IfExpr(r1, r2, r3).setType(lub)

            case None =>
              outOfSubsetError(tr, "Both branches of ifthenelse have incompatible types ("+r2.getType.asString(ctx)+" and "+r3.getType.asString(ctx)+")")
          }

        case ExIsInstanceOf(tt, cc) => {
          val ccRec = extractTree(cc)
          val checkType = extractType(tt.tpe)
          checkType match {
            case cct @ CaseClassType(ccd, tps) => {
              val rootType: LeonClassDef  = if(ccd.parent != None) ccd.parent.get.classDef else ccd

              if(!ccRec.getType.isInstanceOf[ClassType]) {
                outOfSubsetError(tr, "isInstanceOf can only be used with a case class")
              } else {
                val testedExprType = ccRec.getType.asInstanceOf[ClassType].classDef
                val testedExprRootType: LeonClassDef = if(testedExprType.parent != None) testedExprType.parent.get.classDef else testedExprType

                if(rootType != testedExprRootType) {
                  outOfSubsetError(tr, "isInstanceOf can only be used with compatible case classes")
                } else {
                  CaseClassInstanceOf(cct, ccRec)
                }
              }
            }
            case _ => {
              outOfSubsetError(tr, "isInstanceOf can only be used with a case class")
            }
          }
        }


        case pm @ ExPatternMatching(sel, cses) =>
          val rs = extractTree(sel)
          val rc = cses.map(extractMatchCase(_))
          val rt: LeonType = rc.map(_.rhs.getType).reduceLeft(leastUpperBound(_,_).get)
          MatchExpr(rs, rc).setType(rt)

        case t: This =>
          extractType(t.tpe) match {
            case ct: ClassType =>
              LeonThis(ct)
            case _ =>
              outOfSubsetError(t, "Invalid usage of `this`")
          }

        case aup @ ExArrayUpdated(ar, k, v) =>
          val rar = extractTree(ar)
          val rk = extractTree(k)
          val rv = extractTree(v)

          ArrayUpdated(rar, rk, rv)

        case c @ ExCall(rec, sym, tps, args) =>
          val rrec = rec match {
            case t if (defsToDefs contains sym) && !isMethod(sym) =>
              null
            case _ =>
              extractTree(rec)
          }

          val rargs = args.map(extractTree)

          (rrec, sym.name.decoded, rargs) match {
            case (null, _, args) =>
              val fd = getFunDef(sym, c.pos)

              val newTps = tps.map(t => extractType(t.tpe))

              FunctionInvocation(fd.typed(newTps), args).setType(fd.returnType)

            case (IsTyped(rec, ct: ClassType), _, args) if isMethod(sym) =>
              val fd = getFunDef(sym, c.pos)
              val cd = methodToClass(fd)

              val newTps = tps.map(t => extractType(t.tpe))

              MethodInvocation(rec, cd, fd.typed(newTps), args)

            case (IsTyped(rec, cct: CaseClassType), name, Nil) if cct.fields.exists(_.id.name == name) =>

              val fieldID = cct.fields.find(_.id.name == name).get.id

              CaseClassSelector(cct, rec, fieldID)

            // Set methods
            case (IsTyped(a1, SetType(b1)), "min", Nil) =>
              SetMin(a1).setType(b1)

            case (IsTyped(a1, SetType(b1)), "max", Nil) =>
              SetMax(a1).setType(b1)

            case (IsTyped(a1, SetType(b1)), "++", List(IsTyped(a2, SetType(b2))))  if b1 == b2 =>
              SetUnion(a1, a2).setType(SetType(b1))

            case (IsTyped(a1, SetType(b1)), "&", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SetIntersection(a1, a2).setType(SetType(b1))

            case (IsTyped(a1, SetType(b1)), "subsetOf", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SubsetOf(a1, a2)

            case (IsTyped(a1, SetType(b1)), "--", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SetDifference(a1, a2).setType(SetType(b1))

            case (IsTyped(a1, SetType(b1)), "contains", List(a2)) =>
              ElementOfSet(a2, a1)


            // Multiset methods
            case (IsTyped(a1, MultisetType(b1)), "++", List(IsTyped(a2, MultisetType(b2))))  if b1 == b2 =>
              MultisetUnion(a1, a2).setType(MultisetType(b1))

            case (IsTyped(a1, MultisetType(b1)), "&", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetIntersection(a1, a2).setType(MultisetType(b1))

            case (IsTyped(a1, MultisetType(b1)), "--", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetDifference(a1, a2).setType(MultisetType(b1))

            case (IsTyped(a1, MultisetType(b1)), "+++", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetPlus(a1, a2).setType(MultisetType(b1))

            case (IsTyped(_, MultisetType(b1)), "toSet", Nil) =>
              MultisetToSet(rrec).setType(b1)

            // Array methods
            case (IsTyped(a1, ArrayType(vt)), "apply", List(a2)) =>
              ArraySelect(a1, a2).setType(vt)

            case (IsTyped(a1, at: ArrayType), "length", Nil) =>
              ArrayLength(a1)

            case (IsTyped(a1, at: ArrayType), "clone", Nil) =>
              ArrayClone(a1).setType(at)

            case (IsTyped(a1, at: ArrayType), "updated", List(k, v)) =>
              ArrayUpdated(a1, k, v).setType(at)


            // Map methods
            case (IsTyped(a1, MapType(_, vt)), "apply", List(a2)) =>
              MapGet(a1, a2).setType(vt)

            case (IsTyped(a1, mt: MapType), "isDefinedAt", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "contains", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "updated", List(k, v)) =>
              MapUnion(a1, FiniteMap(Seq((k, v))).setType(mt)).setType(mt)

            case (_, name, _) =>
              outOfSubsetError(tr, "Unknown call to "+name)
          }

        // default behaviour is to complain :)
        case _ =>
          outOfSubsetError(tr, "Could not extract as PureScala")
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

      case TypeRef(_, sym, tps) =>
        val leontps = tps.map(extractType)

        if (sym.isAbstractType) {
          if(dctx.tparams contains sym) {
            dctx.tparams(sym)
          } else {
            outOfSubsetError(NoPosition, "Unknown type parameter "+sym)
          }
        } else {
          getClassType(sym, leontps)
        }

      case tt: ThisType =>
        val cd = getClassDef(tt.sym, NoPosition)
        classDefToClassType(cd, cd.tparams.map(_.tp)) // Typed using own's type parameters

      case SingleType(_, sym) =>
        getClassType(sym.moduleClass, Nil)

      case _ =>
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
    }

    private var unknownsToTP        = Map[Symbol, TypeParameter]()

    private def getClassType(sym: Symbol, tps: List[LeonType])(implicit dctx: DefContext) = {
      if (seenClasses contains sym) {
        classDefToClassType(getClassDef(sym, NoPosition), tps)
      } else {
        if (dctx.isProxy) {
          unknownsToTP.getOrElse(sym, {
            val tp = TypeParameter(FreshIdentifier(sym.name.toString, true))
            unknownsToTP += sym -> tp
            tp
          })
        } else {
          outOfSubsetError(NoPosition, "Unknown class "+sym.name)
        }
      }
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
  }

  def containsLetDef(expr: LeonExpr): Boolean = {
    exists { _ match {
      case (l: LetDef) => true
      case _ => false
    }}(expr)
  }
}
