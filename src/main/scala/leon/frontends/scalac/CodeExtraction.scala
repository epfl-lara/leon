/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.reflect.internal.util._

import scala.language.implicitConversions

import purescala._
import Definitions.{
  ClassDef    => LeonClassDef,
  ModuleDef   => LeonModuleDef,
  ValDef      => LeonValDef,
  Import      => LeonImport,
  _
}

import Expressions.{Expr => LeonExpr, This => LeonThis, _}
import Types.{TypeTree => LeonType, _}
import Common._
import Extractors._
import Constructors._
import ExprOps._
import TypeOps._
import xlang.Expressions.{Block => LeonBlock, _}
import xlang.ExprOps._

import leon.utils.{Position => LeonPosition, OffsetPosition => LeonOffsetPosition, RangePosition => LeonRangePosition, Bijection, DefinedPosition}

trait CodeExtraction extends ASTExtractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  val reporter = self.ctx.reporter

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

  def leonPosToScalaPos(spos: global.Position, p: LeonPosition): global.Position = {
    (spos, p) match {
      case (NoPosition, _) =>
        NoPosition

      case (p, dp: DefinedPosition) =>
        new OffsetPosition(p.source, dp.focusBegin.point)

      case _ =>
        NoPosition

    }
  }

  /** An exception thrown when non-purescala compatible code is encountered. */
  sealed class ImpureCodeEncounteredException(pos: Position, msg: String, ot: Option[Tree]) extends Exception(msg) {
    def emit() {
      val debugInfo = if (ctx.findOptionOrDefault(SharedOptions.optDebug) contains utils.DebugSectionTrees) {
        ot.map { t =>
          val strWr = new java.io.StringWriter()
          new global.TreePrinter(new java.io.PrintWriter(strWr)).printTree(t)
          " (Tree: "+strWr.toString+" ; Class: "+t.getClass+")"
        }.getOrElse("")
      } else {
        ""
      }

      if (ctx.findOptionOrDefault(ExtractionPhase.optStrictCompilation)) {
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

  // Simple case classes to capture the representation of units/modules after discovering them.
  case class ScalaUnit(
    name : String,
    pack : PackageRef,
    imports : List[Import],
    defs : List[Tree],
    isPrintable : Boolean
  )

  class Extraction(units: List[CompilationUnit]) {

    case class DefContext(tparams: Map[Symbol, TypeParameter] = Map(),
                          vars: Map[Symbol, () => LeonExpr] = Map(),
                          mutableVars: Map[Symbol, () => LeonExpr] = Map(),
                          isExtern: Boolean = false){

      def union(that: DefContext) = {
        copy(this.tparams ++ that.tparams,
             this.vars ++ that.vars,
             this.mutableVars ++ that.mutableVars,
             this.isExtern || that.isExtern)
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

    private var currentFunDef: FunDef = null

    //This is a bit misleading, if an expr is not mapped then it has no owner, if it is mapped to None it means
    //that it can have any owner
    private var owners: Map[Identifier, Option[FunDef]] = Map()

    // This one never fails, on error, it returns Untyped
    def leonType(tpt: Type)(implicit dctx: DefContext, pos: Position): LeonType = {
      try {
        extractType(tpt)
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.emit()
          Untyped
      }
    }

    private def isIgnored(s: Symbol) = {
      (annotationsOf(s) contains "ignore") || s.fullName.toString.endsWith(".main")
    }

    private def isLibrary(u: CompilationUnit) = Build.libFiles contains u.source.file.absolute.path

    def extractProgram: Option[Program] = {
      try {
        val scalaUnits = units.map { u => u.body match {
          // package object
          case PackageDef(refTree, List(PackageDef(inner, body))) =>
            val name = extractPackageRef(inner).mkString("$")
            val pack = extractPackageRef(refTree) ++ extractPackageRef(inner)
            val imps = imports.getOrElse(refTree, Nil)

            ScalaUnit(name, pack, imps, body, !isLibrary(u))

          // normal package
          case pd@PackageDef(refTree, lst) =>
            val name = u.source.file.name.replaceFirst("[.][^.]+$", "")
            val pack = extractPackageRef(refTree)
            val imps = imports.getOrElse(refTree, Nil)

            ScalaUnit(name, pack, imps, lst, !isLibrary(u))

          case _ =>
            outOfSubsetError(u.body, "Unexpected Unit body")
        }}

        // Phase 1, we discover and define objects/classes/types
        for (unit <- scalaUnits) collectClassSymbols(unit.defs)

        // Phase 2, build scafolding program with empty bodies
        val leonUnits = scalaUnits.map { createLeonUnit }

        // Phase 3, define bodies of all functions/methods
        for (unit <- scalaUnits) fillLeonUnit(unit)

        val pgm0 = Program(leonUnits)

        // Phase 4, resolve imports
        val leonUnits1 = for ((sunit, lunit) <- scalaUnits zip leonUnits) yield {
          val imports = sunit.imports.flatMap(i => extractImport(i, lunit)(pgm0))
          lunit.copy(imports = imports)
        }

        val pgm1 = Program(leonUnits1)

        Some(pgm1)
      } catch {
        case icee: ImpureCodeEncounteredException =>
          icee.emit()
          None
      }
    }

    private def collectClassSymbols(defs: List[Tree]) {
      // We collect all defined classes
      for (t <- defs if !t.isEmpty) t match {
        case t if isIgnored(t.symbol) =>
          // ignore

        case ExAbstractClass(o2, sym, tmpl) =>
          seenClasses += sym -> ((Nil, tmpl))

        case ExCaseClass(o2, sym, args, tmpl) =>
          seenClasses += sym -> ((args, tmpl))

        case ExObjectDef(n, templ) =>
          for (t <- templ.body if !t.isEmpty) t match {
            case t if isIgnored(t.symbol) =>
              // ignore

            case ExAbstractClass(_, sym, tmpl) =>
              seenClasses += sym -> ((Nil, tmpl))

            case ExCaseClass(_, sym, args, tmpl) =>
              seenClasses += sym -> ((args, tmpl))

            case _ =>
          }

        case _ =>
      }
    }

    private def createLeonUnit(u: ScalaUnit): UnitDef = {
      val ScalaUnit(name, pack, _, defs, isPrintable) = u

      val leonDefs = defs flatMap {
        case t if isIgnored(t.symbol) =>
          // ignore
          None

        case t @ ExAbstractClass(o2, sym, _) =>
          Some(getClassDef(sym, t.pos))

        case t @ ExCaseClass(o2, sym, args, _) =>
          Some(getClassDef(sym, t.pos))

        case t @ ExObjectDef(n, templ) =>
          // Module
          val id = FreshIdentifier(n)
          val leonDefs = templ.body.flatMap {
            case t if isIgnored(t.symbol) =>
              // ignore
              None

            case ExAbstractClass(_, sym, _) =>
              Some(getClassDef(sym, t.pos))

            case ExCaseClass(_, sym, _, _) =>
              Some(getClassDef(sym, t.pos))

            // Functions
            case ExFunctionDef(sym, _, _, _, _) =>
              Some(defineFunDef(sym)(DefContext()))

            // Default value functions
            case ExDefaultValueFunction(sym, _, _, _ ,_ , _, _) =>
              val fd = defineFunDef(sym)(DefContext())
              fd.addFlag(IsSynthetic)

              Some(fd)

            // Lazy vals
            case ExLazyAccessorFunction(sym, _, _)  =>
              Some(defineFieldFunDef(sym, true)(DefContext()))

            // Normal vals
            case ExFieldDef(sym, _, _) =>
              Some(defineFieldFunDef(sym, false)(DefContext()))

            // All these are expected, but useless
            case ExCaseClassSyntheticJunk()
               | ExConstructorDef()
               | ExLazyFieldDef()
               | ExFieldAccessorFunction() =>
              None
            case d if (d.symbol.isImplicit && d.symbol.isSynthetic) =>
              None

            // Everything else is unexpected
            case tree =>
              println(tree)
              outOfSubsetError(tree, "Don't know what to do with this. Not purescala?");
          }

          Some(LeonModuleDef(id, leonDefs, id.name == "package"))

        // Expected, but useless
        case ExCaseClassSyntheticJunk() | ExConstructorDef() => None
        case d if (d.symbol.isImplicit && d.symbol.isSynthetic) => None

        // Unexpected
        case tree =>
          println(tree)
          outOfSubsetError(tree, "Don't know what to do with this. Not purescala?");
      }

      // we only resolve imports once we have the full program
      UnitDef(FreshIdentifier(name), pack, Nil, leonDefs, isPrintable)
    }

    private def fillLeonUnit(u: ScalaUnit): Unit = {
      for (t <- u.defs) t match {
        case t if isIgnored(t.symbol) =>
          // ignore

        case ExAbstractClass(_, sym, tpl) =>
          for (t <- tpl.body if !t.isEmpty) {
            extractFunOrMethodBody(Some(sym), t)
          }

        case ExCaseClass(_, sym, _, tpl) =>
          for (t <- tpl.body if !t.isEmpty) {
            extractFunOrMethodBody(Some(sym), t)
          }

        case ExObjectDef(n, templ) =>
          for (t <- templ.body if !t.isEmpty) t match {
            case t if isIgnored(t.symbol) =>
              // ignore
              None

            case ExAbstractClass(_, sym, tpl) =>
              for (t <- tpl.body if !t.isEmpty) {
                extractFunOrMethodBody(Some(sym), t)
              }

            case ExCaseClass(_, sym, _, tpl) =>
              for (t <- tpl.body if !t.isEmpty) {
                extractFunOrMethodBody(Some(sym), t)
              }

            case t =>
              extractFunOrMethodBody(None, t)

          }
        case _ =>
      }
    }

    private def getSelectChain(e: Tree): List[String] = {
      def rec(e: Tree): List[Name] = e match {
        case Select(q, name) => name :: rec(q)
        case Ident(name) => List(name)
        case EmptyTree => List()
        case _ =>
          ctx.reporter.internalError("getSelectChain: unexpected Tree:\n" + e.toString)
      }
      rec(e).reverseMap(_.toString)
    }

    private def extractPackageRef(refPath: RefTree): PackageRef = {
      (getSelectChain(refPath.qualifier) :+ refPath.name.toString).filter(_ != "<empty>")
    }

    private def extractImport(i: Import, current: UnitDef)(implicit pgm: Program): Seq[LeonImport] = {
      val Import(expr, sels) = i
      import DefOps._

      val prefix = getSelectChain(expr)

      val allSels = sels map { prefix :+ _.name.toString }

      // Make a different import for each selector at the end of the chain
      allSels flatMap { selectors =>
        assert(selectors.nonEmpty)
        val (thePath, isWild) = selectors.last match {
          case "_" => (selectors.dropRight(1), true)
          case _   => (selectors, false)
        }

        Some(LeonImport(thePath, isWild))
      }
    }

    private var seenClasses = Map[Symbol, (Seq[(Symbol, ValDef)], Template)]()
    private var classesToClasses  = Map[Symbol, LeonClassDef]()

    def oracleType(pos: Position, tpe: LeonType) = {
      classesToClasses.find {
        case (sym, cl) => sym.fullName.toString == "leon.lang.synthesis.Oracle"
      } match {
        case Some((_, cd)) =>
          cd.typed(List(tpe))
        case None =>
          outOfSubsetError(pos, "Could not find class Oracle")
      }
    }

    def libraryClass(pos: Position, className: String): LeonClassDef = {
      classesToClasses.find{ case (s, c) => s.fullName == className }.map(_._2).getOrElse {
        outOfSubsetError(pos, "Could not find class "+className)
      }
    }

    def libraryCaseClass(pos: Position, className: String): CaseClassDef = {
      libraryClass(pos, className) match {
        case ccd: CaseClassDef => ccd
        case _ =>
          outOfSubsetError(pos, "Class "+className+" is not a case class")
      }
    }


    private var paramsToDefaultValues = Map[Symbol,FunDef]()


    def getClassDef(sym: Symbol, pos: Position): LeonClassDef = {
      classesToClasses.get(sym) match {
        case Some(cd) => cd
        case None =>
          if (seenClasses contains sym) {
            val (args, tmpl) = seenClasses(sym)

            extractClassDef(sym, args, tmpl)
          } else {
            outOfSubsetError(pos, "Class "+sym.fullName+" not defined?")
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

    /**
     * For the function in $defs with name $owner, find its parameter with index $index,
     * and registers $fd as the default value function for this parameter.
     */
    private def registerDefaultMethod(
      defs : List[Tree],
      matcher : PartialFunction[Tree,Symbol],
      index : Int,
      fd : FunDef
    )  {
      // Search tmpl to find the function that includes this parameter
      val paramOwner = defs.collectFirst(matcher).get

      // assumes single argument list
      if(paramOwner.paramss.length != 1) {
        outOfSubsetError(paramOwner.pos, "Multiple argument lists for a function are not allowed")
      }
      val theParam = paramOwner.paramss.head(index)
      paramsToDefaultValues += (theParam -> fd)
    }

    def extractClassDef(sym: Symbol, args: Seq[(Symbol, ValDef)], tmpl: Template): LeonClassDef = {

      //println(s"Extracting $sym")

      val id = FreshIdentifier(sym.name.toString).setPos(sym.pos)

      val tparamsMap = sym.tpe match {
        case TypeRef(_, _, tps) =>
          extractTypeParams(tps)
        case _ =>
          Nil
      }

      val parent = sym.tpe.parents.headOption match {
        case Some(TypeRef(_, parentSym, tps)) if seenClasses contains parentSym =>
          getClassDef(parentSym, sym.pos) match {
            case acd: AbstractClassDef =>
              val defCtx = DefContext(tparamsMap.toMap)
              val newTps = tps.map(extractType(_)(defCtx, sym.pos))
              val zip = (newTps zip tparamsMap.map(_._2))
              if (newTps.size != tparamsMap.size) {
                outOfSubsetError(sym.pos, "Child classes should have the same number of type parameters as their parent")
                None
              } else if (zip.exists {
                case (TypeParameter(_), _) => false
                case _ => true
              }) {
                outOfSubsetError(sym.pos, "Child class type params should have a simple mapping to parent params")
                None
              } else if (zip.exists {
                case (TypeParameter(id), ctp) => id.name != ctp.id.name
                case _ => false
              }) {
                outOfSubsetError(sym.pos, "Child type params should be identical to parent class's (e.g. C[T1,T2] extends P[T1,T2])")
                None
              } else {
                Some(acd.typed -> acd.tparams)
              }

            case cd =>
              outOfSubsetError(sym.pos, s"Class $id cannot extend ${cd.id}")
              None
          }

        case p =>
          None
      }

      val tparams = parent match {
        case Some((p, tparams)) => tparams
        case None => tparamsMap.map(t => TypeParameterDef(t._2))
      }

      val defCtx = DefContext((tparamsMap.map(_._1) zip tparams.map(_.tp)).toMap)

      // Extract class
      val cd = if (sym.isAbstractClass) {
        AbstractClassDef(id, tparams, parent.map(_._1))
      } else  {
        CaseClassDef(id, tparams, parent.map(_._1), sym.isModuleClass)
      }
      cd.setPos(sym.pos)
      //println(s"Registering $sym")
      classesToClasses += sym -> cd
      cd.addFlags(annotationsOf(sym).map { case (name, args) => ClassFlag.fromName(name, args) }.toSet)

      // Register parent
      parent.map(_._1).foreach(_.classDef.registerChild(cd))

      // Extract case class fields
      cd match {
        case ccd: CaseClassDef =>

          val fields = args.map { case (fsym, t) =>
            val tpe = leonType(t.tpt.tpe)(defCtx, fsym.pos)
            val id = cachedWithOverrides(fsym, Some(ccd), tpe)
            if (tpe != id.getType) println(tpe, id.getType)
            LeonValDef(id.setPos(t.pos)).setPos(t.pos)
          }
          //println(s"Fields of $sym")
          ccd.setFields(fields)
        case _ =>
      }

      //println(s"Body of $sym")

      // We collect the methods and fields
      for (d <- tmpl.body) d match {
        case EmptyTree =>
          // ignore

        case t if isIgnored(t.symbol) =>
          // ignore

        // Normal methods
        case t @ ExFunctionDef(fsym, _, _, _, _) =>
          isMethod += fsym
          val fd = defineFunDef(fsym, Some(cd))(defCtx)


          methodToClass += fd -> cd

          cd.registerMethod(fd)

        // Default values for parameters
        case t@ ExDefaultValueFunction(fsym, _, _, _, owner, index, _) =>
          isMethod += fsym
          val fd = defineFunDef(fsym)(defCtx)
          fd.addFlag(IsSynthetic)
          methodToClass += fd -> cd

          cd.registerMethod(fd)
          val matcher: PartialFunction[Tree, Symbol] = {
            case ExFunctionDef(ownerSym, _ ,_ ,_, _) if ownerSym.name.toString == owner => ownerSym
          }
          registerDefaultMethod(tmpl.body, matcher, index, fd )

        // Lazy fields
        case t @ ExLazyAccessorFunction(fsym, _, _)  =>
          isMethod += fsym
          val fd = defineFieldFunDef(fsym, true, Some(cd))(defCtx)
          methodToClass += fd -> cd

          cd.registerMethod(fd)

        // normal fields
        case t @ ExFieldDef(fsym, _, _) =>
          //println(fsym + "matched as ExFieldDef")
          // we will be using the accessor method of this field everywhere
          isMethod += fsym
          val fd = defineFieldFunDef(fsym, false, Some(cd))(defCtx)
          methodToClass += fd -> cd

          cd.registerMethod(fd)

        case other =>

      }

      //println(s"End body $sym")

      cd
    }

    // Returns the parent's method Identifier if sym overrides a symbol, otherwise a fresh Identifier

    private val funOrFieldSymsToIds = new Bijection[Symbol, Identifier]

    private def cachedWithOverrides(sym: Symbol, within: Option[LeonClassDef], tpe: LeonType = Untyped) = {

      val topOfHierarchy = sym.overrideChain.last

      funOrFieldSymsToIds.cachedB(topOfHierarchy){
        FreshIdentifier(sym.name.toString, tpe)
      }
    }

    private var defsToDefs = Map[Symbol, FunDef]()

    private def defineFunDef(sym: Symbol, within: Option[LeonClassDef] = None)(implicit dctx: DefContext): FunDef = {
      // Type params of the function itself
      val tparams = extractTypeParams(sym.typeParams.map(_.tpe))

      val nctx = dctx.copy(tparams = dctx.tparams ++ tparams.toMap)

      val newParams = sym.info.paramss.flatten.map{ sym =>
        val ptpe = leonType(sym.tpe)(nctx, sym.pos)
        val tpe = if (sym.isByNameParam) FunctionType(Seq(), ptpe) else ptpe
        val newID = FreshIdentifier(sym.name.toString, tpe).setPos(sym.pos)
        owners += (newID -> None)
        LeonValDef(newID, sym.isByNameParam).setPos(sym.pos)
      }

      val tparamsDef = tparams.map(t => TypeParameterDef(t._2))

      val returnType = leonType(sym.info.finalResultType)(nctx, sym.pos)

      // @mk: We type the identifiers of methods during code extraction because
      // a possible implementing/overriding field will use this same Identifier
      val idType = {
        val argTypes = newParams map { _.getType }
        if (argTypes.nonEmpty) FunctionType(argTypes, returnType)
        else returnType
      }

      val id = cachedWithOverrides(sym, within, idType)

      val fd = new FunDef(id.setPos(sym.pos), tparamsDef, newParams, returnType)

      fd.setPos(sym.pos)

      fd.addFlags(annotationsOf(sym).map { case (name, args) => FunctionFlag.fromName(name, args) }.toSet)

      if (sym.isImplicit) {
        fd.addFlag(IsInlined)
      }

      defsToDefs += sym -> fd

      fd
    }

    private def defineFieldFunDef(sym : Symbol, isLazy : Boolean, within: Option[LeonClassDef] = None)(implicit dctx : DefContext) : FunDef = {

      val nctx = dctx.copy(tparams = dctx.tparams)

      val returnType = leonType(sym.info.finalResultType)(nctx, sym.pos)

      // @mk: We type the identifiers of methods during code extraction because
      // a possible implementing/overriding field will use this same Identifier
      val id = cachedWithOverrides(sym, within, returnType)
      val fd = new FunDef(id.setPos(sym.pos), Seq(), Seq(), returnType)

      fd.setPos(sym.pos)
      fd.addFlag(IsField(isLazy))

      fd.addFlags(annotationsOf(sym).map { case (name, args) => FunctionFlag.fromName(name, args) }.toSet)

      defsToDefs += sym -> fd

      fd
    }

    private def extractFunOrMethodBody(ocsym: Option[Symbol], t: Tree) {

      val ctparamsMap = ocsym match {
        case Some(csym) =>
          val cd = classesToClasses(csym)

          val ctparams = csym.tpe match {
            case TypeRef(_, _, tps) =>
              extractTypeParams(tps).map(_._1)
            case _ =>
              Nil
          }

          ctparams zip cd.tparams.map(_.tp)

        case None =>
          Map[Symbol, TypeParameter]()
      }

      t match {
        case t if isIgnored(t.symbol) =>
          //ignore

        case ExFunctionDef(sym, tparams, params, _, body) =>
          val fd = defsToDefs(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap ++ ctparamsMap

          if(body != EmptyTree) {
            extractFunBody(fd, params, body)(DefContext(tparamsMap))
          }

        // Default value functions
        case ExDefaultValueFunction(sym, tparams, params, _, _, _, body) =>
          val fd = defsToDefs(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap ++ ctparamsMap

          if(body != EmptyTree) {
            extractFunBody(fd, params, body)(DefContext(tparamsMap))
          }

        // Lazy fields
        case t @ ExLazyAccessorFunction(sym, _, body) =>
          val fd = defsToDefs(sym)
          val tparamsMap = ctparamsMap

          if(body != EmptyTree) {
            extractFunBody(fd, Seq(), body)(DefContext(tparamsMap.toMap))
          }

        // normal fields
        case t @ ExFieldDef(sym, _, body) => // if !sym.isSynthetic && !sym.isAccessor =>
          val fd = defsToDefs(sym)
          val tparamsMap = ctparamsMap

          if(body != EmptyTree) {
            extractFunBody(fd, Seq(), body)(DefContext(tparamsMap.toMap))
          }

        case _ =>
      }
    }

    private def extractTypeParams(tps: Seq[Type]): Seq[(Symbol, TypeParameter)] = {
      tps.flatMap {
        case TypeRef(_, sym, Nil) =>
          Some(sym -> TypeParameter.fresh(sym.name.toString))
        case t =>
          outOfSubsetError(t.typeSymbol.pos, "Unhandled type for parameter: "+t)
          None
      }
    }

    //var objects2Objects = Map[Identifier, LeonModuleDef]()

    private def extractFunBody(funDef: FunDef, params: Seq[ValDef], body0 : Tree)(dctx: DefContext): FunDef = {
      currentFunDef = funDef

      // Find defining function for params with default value
      for ((s,vd) <- params zip funDef.params) {
        vd.defaultValue = paramsToDefaultValues.get(s.symbol)
      }

      val newVars = for ((s, vd) <- params zip funDef.params) yield s.symbol -> {
        if (s.symbol.isByNameParam) () => Application(Variable(vd.id), Seq())
        else () => Variable(vd.id)
      }

      val fctx = dctx.withNewVars(newVars).copy(isExtern = funDef.annotations("extern"))

      // If this is a lazy field definition, drop the assignment/ accessing
      val body =
        if (funDef.flags.contains(IsField(true))) { body0 match {
          case Block(List(Assign(_, realBody)),_ ) => realBody
          case _ => outOfSubsetError(body0, "Wrong form of lazy accessor")
        }} else body0

      val finalBody = try {
        flattenBlocks(extractTreeOrNoTree(body)(fctx)) match {
          case e if e.getType.isInstanceOf[ArrayType] =>
            getOwner(e) match {
              case Some(Some(fd)) if fd == funDef =>
                e

              case None =>
                e

              case _ =>
                outOfSubsetError(body, "Function cannot return an array that is not locally defined")
            }
          case e =>
            e
        }
      } catch {
        case e: ImpureCodeEncounteredException =>
          e.emit()
          //val pos = if (body0.pos == NoPosition) NoPosition else leonPosToScalaPos(body0.pos.source, funDef.getPos)
          if (ctx.findOptionOrDefault(ExtractionPhase.optStrictCompilation)) {
            reporter.error(funDef.getPos, "Function "+funDef.id.name+" could not be extracted. The function likely uses features not supported by Leon.")
          } else {
            reporter.warning(funDef.getPos, "Function "+funDef.id.name+" is not fully available to Leon.")
          }

          funDef.addFlag(IsAbstract)
          NoTree(funDef.returnType)
      }

      funDef.fullBody = finalBody

      // Post-extraction sanity checks

      funDef.precondition.foreach { case e =>
        if(containsLetDef(e)) {
          reporter.warning(e.getPos, "Function precondition should not contain nested function definition, ignoring.")
          funDef.precondition = None
        }
      }

      funDef.postcondition.foreach { e =>
        if(containsLetDef(e)) {
          reporter.warning(e.getPos, "Function postcondition should not contain nested function definition, ignoring.")
          funDef.postcondition = None
        }
      }

      funDef
    }

    private def extractPattern(p: Tree, binder: Option[Identifier] = None)(implicit dctx: DefContext): (Pattern, DefContext) = p match {
      case b @ Bind(name, t @ Typed(pat, tpt)) =>
        val newID = FreshIdentifier(name.toString, extractType(tpt)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => Variable(newID)))
        extractPattern(t, Some(newID))(pctx)

      case b @ Bind(name, pat) =>
        val newID = FreshIdentifier(name.toString, extractType(b)).setPos(b.pos)
        val pctx = dctx.withNewVar(b.symbol -> (() => Variable(newID)))
        extractPattern(pat, Some(newID))(pctx)

      case t @ Typed(Ident(nme.WILDCARD), tpt) =>
        extractType(tpt) match {
          case ct: ClassType =>
            (InstanceOfPattern(binder, ct).setPos(p.pos), dctx)

          case lt =>
            outOfSubsetError(tpt, "Invalid type "+tpt.tpe+" for .isInstanceOf")
        }

      case Ident(nme.WILDCARD) =>
        (WildcardPattern(binder).setPos(p.pos), dctx)

      case s @ Select(_, b) if s.tpe.typeSymbol.isCase =>
        // case Obj =>
        extractType(s) match {
          case ct: CaseClassType =>
            assert(ct.classDef.fields.isEmpty)
            (CaseClassPattern(binder, ct, Seq()).setPos(p.pos), dctx)
          case _ =>
            outOfSubsetError(s, "Invalid type "+s.tpe+" for .isInstanceOf")
        }

      case a @ Apply(fn, args) =>

        extractType(a) match {
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

      case ExBigIntPattern(n: Literal) =>
        val lit = InfiniteIntegerLiteral(BigInt(n.value.stringValue))
        (LiteralPattern(binder, lit), dctx)

      case ExInt32Literal(i)   => (LiteralPattern(binder, IntLiteral(i)),     dctx)
      case ExBooleanLiteral(b) => (LiteralPattern(binder, BooleanLiteral(b)), dctx)
      case ExUnitLiteral()     => (LiteralPattern(binder, UnitLiteral()),     dctx)
      case ExStringLiteral(s)  => (LiteralPattern(binder, StringLiteral(s)),  dctx)
        
      case up@ExUnapplyPattern(s, args) =>
        implicit val p: Position = NoPosition
        val fd = getFunDef(s, up.pos)
        val (sub, ctx) = args.map (extractPattern(_)).unzip
        val unapplyMethod = defsToDefs(s)
        val formalTypes = tupleTypeWrap(
          unapplyMethod.params.map { _.getType } ++
          unapplyMethod.returnType.asInstanceOf[ClassType].tps
        )
        val realTypes = tupleTypeWrap(Seq(
          extractType(up.tpe),
          tupleTypeWrap(args map { tr => extractType(tr.tpe)})
        ))
        val newTps = canBeSubtypeOf(realTypes, typeParamsOf(formalTypes).toSeq, formalTypes) match {
          case Some(tmap) =>
            fd.tparams map { tpd => tmap.getOrElse(tpd.tp, tpd.tp) }
          case None =>
            reporter.fatalError("Could not instantiate type of unapply method")
        }

        (UnapplyPattern(binder, fd.typed(newTps), sub).setPos(up.pos), ctx.foldLeft(dctx)(_ union _))

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

    private def extractTreeOrNoTree(tr: Tree)(implicit dctx: DefContext): LeonExpr = {
      try {
        val res = extractTree(tr)
        if (dctx.isExtern) {
          reporter.warning(res.getPos, "External function could be extracted as Leon tree")
        }
        res
      } catch {
        case e: ImpureCodeEncounteredException =>
          if (dctx.isExtern) {
            NoTree(extractType(tr)).setPos(tr.pos)
          } else {
            throw e
          }
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
        case Block(Nil, last) =>
          (last, None)
        case e =>
          (e, None)
      }

      var rest = tmpRest

      val res = current match {
        case ExEnsuredExpression(body, contract) =>
          val post = extractTree(contract)

          val b = extractTreeOrNoTree(body)

          val closure = post match {
            case IsTyped(_, BooleanType) =>
              val resId = FreshIdentifier("res", b.getType).setPos(post)
              Lambda(Seq(LeonValDef(resId)), post).setPos(post)
            case l: Lambda => l
            case other =>
              val resId = FreshIdentifier("res", b.getType).setPos(post)
              Lambda(Seq(LeonValDef(resId)), application(other, Seq(Variable(resId)))).setPos(post)
          }

          Ensuring(b, closure)

        case t @ ExHoldsExpression(body) =>
          val resId = FreshIdentifier("holds", BooleanType).setPos(current.pos)
          val post = Lambda(Seq(LeonValDef(resId)), Variable(resId)).setPos(current.pos)

          val b = extractTreeOrNoTree(body)

          Ensuring(b, post)

        case ExAssertExpression(contract, oerr) =>
          val const = extractTree(contract)
          val b     = rest.map(extractTreeOrNoTree).getOrElse(UnitLiteral())

          rest = None

          Assert(const, oerr, b)

        case ExRequiredExpression(contract) =>
          val pre = extractTree(contract)

          val b = rest.map(extractTreeOrNoTree).getOrElse(UnitLiteral())

          rest = None

          Require(pre, b)

        case ExPasses(in, out, cases) =>
          val ine = extractTree(in)
          val oute = extractTree(out)
          val rc = cases.map(extractMatchCase)

          // @mk: FIXME: this whole sanity checking is very dodgy at best.
          val ines = unwrapTuple(ine, ine.isInstanceOf[Tuple]) // @mk We untuple all tuples
          ines foreach {
            case v @ Variable(_) if currentFunDef.params.map{ _.toVariable } contains v =>
            case LeonThis(_) =>
            case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
          }
          oute match {
            case Variable(_) => // FIXME: this is not strict enough, we need the bound variable of enclosing Ensuring
            case other => ctx.reporter.fatalError(other.getPos, "Only i/o variables are allowed in i/o examples")
          }
          passes(ine, oute, rc)

        case ExArrayLiteral(tpe, args) =>
          finiteArray(args.map(extractTree), None, extractType(tpe)(dctx, current.pos))

        case ExCaseObject(sym) =>
          getClassDef(sym, current.pos) match {
            case ccd: CaseClassDef =>
              CaseClass(CaseClassType(ccd, Seq()), Seq())
            case _ =>
              outOfSubsetError(current, "Unknown case object "+sym.name)
          }

        case ExTuple(tpes, exprs) =>
          val tupleExprs = exprs.map(e => extractTree(e))
          Tuple(tupleExprs)

        case ex@ExOldExpression(sym) if dctx.isVariable(sym) =>
          dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
            case Some(builder) =>
              val Variable(id) = builder()
              Old(id).setPos(ex.pos)
            case None =>
              outOfSubsetError(current, "old can only be used with variables")
          }

        case ExErrorExpression(str, tpt) =>
          Error(extractType(tpt), str)

        case ExTupleExtract(tuple, index) =>
          val tupleExpr = extractTree(tuple)

          tupleExpr.getType match {
            case TupleType(tpes) if tpes.size >= index =>
              tupleSelect(tupleExpr, index, true)

            case _ =>
              outOfSubsetError(current, "Invalid tuple access")
          }

        case ExValDef(vs, tpt, bdy) =>
          val binderTpe = extractType(tpt)
          val newID = FreshIdentifier(vs.name.toString, binderTpe)
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
            case Some(rst) =>
              val nctx = dctx.withNewVar(vs -> (() => Variable(newID)))
              extractTree(rst)(nctx)
            case None =>
              UnitLiteral()
          }

          rest = None
          Let(newID, valTree, restTree)


        case d @ ExFunctionDef(sym, tparams, params, ret, b) =>
          val fd = defineFunDef(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          fd.addFlags(annotationsOf(d.symbol).map { case (name, args) => FunctionFlag.fromName(name, args) }.toSet)

          val newDctx = dctx.copy(tparams = dctx.tparams ++ tparamsMap)

          val restTree = rest match {
            case Some(rst) => extractTree(rst)
            case None => UnitLiteral()
          }
          rest = None
          
          val oldCurrentFunDef = currentFunDef

          val funDefWithBody = extractFunBody(fd, params, b)(newDctx)

          currentFunDef = oldCurrentFunDef
          
          val (other_fds, block) = restTree match {
            case LetDef(fds, block) =>
              (fds, block)
            case _ =>
              (Nil, restTree)
          }
          LetDef(funDefWithBody +: other_fds, block)

        // FIXME case ExDefaultValueFunction

        /**
         * XLang Extractors
         */

        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = extractType(tpt)
          val newID = FreshIdentifier(vs.name.toString, binderTpe)
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

        case epsi @ ExEpsilonExpression(tpt, varSym, predBody) =>
          val pstpe = extractType(tpt)
          val nctx = dctx.withNewVar(varSym -> (() => EpsilonVariable(epsi.pos, pstpe)))
          val c1 = extractTree(predBody)(nctx)
          if(containsEpsilon(c1)) {
            outOfSubsetError(epsi, "Usage of nested epsilon is not allowed")
          }
          Epsilon(c1, pstpe)

        case ExWaypointExpression(tpt, i, tree) =>
          val pstpe = extractType(tpt)
          val IntLiteral(ri) = extractTree(i)
          Waypoint(ri, extractTree(tree), pstpe)

        case update @ ExUpdate(lhs, index, newValue) =>
          val lhsRec = extractTree(lhs)
          lhsRec match {
            case Variable(_) =>
            case _ =>
              outOfSubsetError(tr, "Array update only works on variables")
          }

          getOwner(lhsRec) match {
          //  case Some(Some(fd)) if fd != currentFunDef =>
          //    outOfSubsetError(tr, "cannot update an array that is not defined locally")

          //  case Some(None) =>
          //    outOfSubsetError(tr, "cannot update an array that is not defined locally")

            case Some(_) =>

            case None => sys.error("This array: " + lhsRec + " should have had an owner")
          }

          val indexRec = extractTree(index)
          val newValueRec = extractTree(newValue)
          ArrayUpdate(lhsRec, indexRec, newValueRec)

        case ExBigIntLiteral(n: Literal) =>
          InfiniteIntegerLiteral(BigInt(n.value.stringValue))

        case ExBigIntLiteral(n) => outOfSubsetError(tr, "Non-literal BigInt constructor")

        case ExIntToBigInt(tree) =>
          val rec = extractTree(tree)
          rec match {
            case IntLiteral(n) =>
              InfiniteIntegerLiteral(BigInt(n))
            case _ =>
              outOfSubsetError(tr, "Conversion from Int to BigInt")
          }

        case ExRealLiteral(n, d) =>
          val rn = extractTree(n)
          val rd = extractTree(d)
          (rn, rd) match {
            case (InfiniteIntegerLiteral(n), InfiniteIntegerLiteral(d)) =>
              FractionalLiteral(n, d)
            case _ =>
              outOfSubsetError(tr, "Real not build from literals")
          }
        case ExRealIntLiteral(n) =>
          val rn = extractTree(n)
          rn match {
            case InfiniteIntegerLiteral(n) =>
              FractionalLiteral(n, 1)
            case _ =>
              outOfSubsetError(tr, "Real not build from literals")
          }

        case ExInt32Literal(v) =>
          IntLiteral(v)

        case ExBooleanLiteral(v) =>
          BooleanLiteral(v)

        case ExUnitLiteral() =>
          UnitLiteral()

        case ExLocally(body) =>
          extractTree(body)

        case ExTyped(e, _) =>
          // TODO: refine type here?
          extractTree(e)

        case ex @ ExIdentifier(sym, tpt) if dctx.isVariable(sym) || defsToDefs.contains(sym) =>
          dctx.vars.get(sym).orElse(dctx.mutableVars.get(sym)) match {
            case Some(builder) =>
              builder().setPos(ex.pos)
            case None =>
              // Maybe it is a function
              defsToDefs.get(sym) match {
                case Some(fd) =>
                  FunctionInvocation(fd.typed, Seq()).setPos(sym.pos)
                case None =>
                  outOfSubsetError(tr, "Unidentified variable " + sym + " " + sym.id + ".")
              }
          }

        case hole @ ExHoleExpression(tpt, exprs) =>
          Hole(extractType(tpt), exprs.map(extractTree))

        case ops @ ExWithOracleExpression(oracles, body) =>
          val newOracles = oracles map { case (tpt, sym) =>
            val aTpe  = extractType(tpt)
            val oTpe  = oracleType(ops.pos, aTpe)
            val newID = FreshIdentifier(sym.name.toString, oTpe)
            owners += (newID -> None)
            newID
          }

          val newVars = (oracles zip newOracles).map {
            case ((_, sym), id) =>
              sym -> (() => Variable(id))
          }

          val cBody = extractTree(body)(dctx.withNewVars(newVars))

          WithOracle(newOracles, cBody)


        case chs @ ExChooseExpression(body) =>
          val cBody = extractTree(body)
          Choose(cBody)

        case l @ ExLambdaExpression(args, body) =>
          val vds = args map { vd =>
            val aTpe = extractType(vd.tpt)
            val newID = FreshIdentifier(vd.symbol.name.toString, aTpe)
            owners += (newID -> None)
            LeonValDef(newID)
          }

          val newVars = (args zip vds).map { case (vd, lvd) =>
            vd.symbol -> (() => lvd.toVariable)
          }

          val exBody = extractTree(body)(dctx.withNewVars(newVars))

          Lambda(vds, exBody)

        case ExForallExpression(args, body) =>
          val vds = args map { case (tpt, sym) =>
            val aTpe = extractType(tpt)
            val newID = FreshIdentifier(sym.name.toString, aTpe)
            owners += (newID -> None)
            LeonValDef(newID)
          }

          val newVars = (args zip vds).map { case ((_, sym), lvd) =>
            sym -> (() => lvd.toVariable)
          }

          val exBody = extractTree(body)(dctx.withNewVars(newVars))

          Forall(vds, exBody)

        case ExFiniteMap(tptFrom, tptTo, args) =>
          val singletons = args.collect {
            case ExTuple(tpes, trees) if trees.size == 2 =>
              (extractTree(trees(0)), extractTree(trees(1)))
          }.toMap

          if (singletons.size != args.size) {
            outOfSubsetError(tr, "Some map elements could not be extracted as Tuple2")
          }

          FiniteMap(singletons, extractType(tptFrom), extractType(tptTo))

        case ExFiniteSet(tpt, args) =>
          FiniteSet(args.map(extractTree).toSet, extractType(tpt))

        case ExCaseClassConstruction(tpt, args) =>
          extractType(tpt) match {
            case cct: CaseClassType =>
              CaseClass(cct, args.map(extractTree))

            case _ =>
              outOfSubsetError(tr, "Construction of a non-case class.")

          }

        case ExNot(e)        => Not(extractTree(e))
        case ExUMinus(e)     => UMinus(extractTree(e))
        case ExRealUMinus(e) => RealUMinus(extractTree(e))
        case ExBVUMinus(e)   => BVUMinus(extractTree(e))
        case ExBVNot(e)      => BVNot(extractTree(e))

        case ExNotEquals(l, r) =>
          val rl = extractTree(l)
          val rr = extractTree(r)

          (rl, rr) match {
            case (IsTyped(_, rt), IsTyped(_, lt)) if typesCompatible(lt, rt) =>
              Not(Equals(rl, rr))

            case (IntLiteral(v), IsTyped(_, IntegerType)) =>
              Not(Equals(InfiniteIntegerLiteral(v), rr))

            case (IsTyped(_, IntegerType), IntLiteral(v)) =>
              Not(Equals(rl, InfiniteIntegerLiteral(v)))

            case (IsTyped(_, rt), IsTyped(_, lt)) =>
              outOfSubsetError(tr, "Invalid comparison: (_: "+rt.asString+") != (_: "+lt.asString+")")
          }

        case ExEquals(l, r) =>
          val rl = extractTree(l)
          val rr = extractTree(r)

          (rl, rr) match {
            case (IsTyped(_, rt), IsTyped(_, lt)) if typesCompatible(lt, rt) =>
              Equals(rl, rr)

            case (IntLiteral(v), IsTyped(_, IntegerType)) =>
              Equals(InfiniteIntegerLiteral(v), rr)

            case (IsTyped(_, IntegerType), IntLiteral(v)) =>
              Equals(rl, InfiniteIntegerLiteral(v))

            case (IsTyped(_, rt), IsTyped(_, lt)) =>
              outOfSubsetError(tr, "Invalid comparison: (_: "+rt+") == (_: "+lt+")")
          }

        case ExArrayFill(baseType, length, defaultValue) =>
          val lengthRec = extractTree(length)
          val defaultValueRec = extractTree(defaultValue)
          NonemptyArray(Map(), Some(defaultValueRec, lengthRec))

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
              IfExpr(r1, r2, r3)

            case None =>
              outOfSubsetError(tr, "Both branches of ifthenelse have incompatible types ("+r2.getType.asString(ctx)+" and "+r3.getType.asString(ctx)+")")
          }

        case ExAsInstanceOf(expr, tt) =>
          val eRec = extractTree(expr)
          val checkType = extractType(tt)
          checkType match {
            case ct: ClassType =>
              AsInstanceOf(eRec, ct)
            case _ =>
              outOfSubsetError(tr, "asInstanceOf can only cast to class types")
          }

        case ExIsInstanceOf(tt, cc) =>
          val ccRec = extractTree(cc)
          val checkType = extractType(tt)
          checkType match {
            case ct: ClassType =>
              if(!ccRec.getType.isInstanceOf[ClassType]) {
                outOfSubsetError(tr, "isInstanceOf can only be used with a class")
              } else {
                val rootType: LeonClassDef  = ct.root.classDef
                val testedExprType = ccRec.getType.asInstanceOf[ClassType]
                val testedExprRootType: LeonClassDef = testedExprType.root.classDef

                if(rootType != testedExprRootType) {
                  outOfSubsetError(tr, "isInstanceOf can only be used with compatible classes")
                } else {
                  IsInstanceOf(ccRec, ct)
                }
              }
            case _ =>
              outOfSubsetError(tr, "isInstanceOf can only be used with a class")
          }

        case pm @ ExPatternMatching(sel, cses) =>
          val rs = extractTree(sel)
          val rc = cses.map(extractMatchCase)
          matchExpr(rs, rc)

        case t: This =>
          extractType(t) match {
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

        case l @ ExListLiteral(tpe, elems) =>
          val rtpe = extractType(tpe)
          val cons = CaseClassType(libraryCaseClass(l.pos, "leon.collection.Cons"), Seq(rtpe))
          val nil  = CaseClassType(libraryCaseClass(l.pos, "leon.collection.Nil"),  Seq(rtpe))

          elems.foldRight(CaseClass(nil, Seq())) {
            case (e, ls) => CaseClass(cons, Seq(extractTree(e), ls))
          }

        case chr @ ExCharLiteral(c) =>
          CharLiteral(c)

        case str @ ExStringLiteral(s) =>
          StringLiteral(s)

        case ExImplies(lhs, rhs) =>
          Implies(extractTree(lhs), extractTree(rhs)).setPos(current.pos)

        case ExStringEscape(s) =>
          StringEscape(extractTree(s))
          
        case c @ ExCall(rec, sym, tps, args) =>
          // The object on which it is called is null if the symbol sym is a valid function in the scope and not a method.
          val rrec = rec match {
            case t if (defsToDefs contains sym) && !isMethod(sym) =>
              null
            case _ =>
              extractTree(rec)
          }

          val rargs = args.map(extractTree)

          //println(s"symbol $sym with id ${sym.id}")
          //println(s"isMethod($sym) == ${isMethod(sym)}")

          (rrec, sym.name.decoded, rargs) match {
            case (null, _, args) =>
              val fd = getFunDef(sym, c.pos)

              val newTps = tps.map(t => extractType(t))
              val argsByName = (fd.params zip args).map(p => if (p._1.isLazy) Lambda(Seq(), p._2) else p._2)

              FunctionInvocation(fd.typed(newTps), argsByName)

            case (IsTyped(rec, ct: ClassType), _, args) if isMethod(sym) =>
              val fd = getFunDef(sym, c.pos)
              val cd = methodToClass(fd)

              val newTps = tps.map(t => extractType(t))
              val argsByName = (fd.params zip args).map(p => if (p._1.isLazy) Lambda(Seq(), p._2) else p._2)

              MethodInvocation(rec, cd, fd.typed(newTps), argsByName)

            case (IsTyped(rec, ft: FunctionType), _, args) =>
              application(rec, args)

            case (IsTyped(rec, cct: CaseClassType), name, Nil) if cct.classDef.fields.exists(_.id.name == name) =>
              val fieldID = cct.classDef.fields.find(_.id.name == name).get.id

              caseClassSelector(cct, rec, fieldID)

            //String methods
            case (IsTyped(a1, StringType), "toString", List()) =>
              a1
            case (IsTyped(a1, WithStringconverter(converter)), "toString", List()) =>
              converter(a1)
            case (IsTyped(a1, StringType), "+", List(IsTyped(a2, StringType))) =>
              StringConcat(a1, a2)
            case (IsTyped(a1, StringType), "+", List(IsTyped(a2, WithStringconverter(converter)))) =>
              StringConcat(a1, converter(a2))
            case (IsTyped(a1, WithStringconverter(converter)), "+", List(IsTyped(a2, StringType))) =>
              StringConcat(converter(a1), a2)
            case (IsTyped(a1, StringType), "length", List()) =>
              StringLength(a1)
            case (IsTyped(a1, StringType), "substring", List(IsTyped(start, IntegerType | Int32Type))) =>
              SubString(a1, start, StringLength(a1))
            case (IsTyped(a1, StringType), "substring", List(IsTyped(start, IntegerType | Int32Type), IsTyped(end, IntegerType | Int32Type))) =>
              SubString(a1, start, end)
            //BigInt methods
            case (IsTyped(a1, IntegerType), "+", List(IsTyped(a2, IntegerType))) =>
              Plus(a1, a2)
            case (IsTyped(a1, IntegerType), "-", List(IsTyped(a2, IntegerType))) =>
              Minus(a1, a2)
            case (IsTyped(a1, IntegerType), "*", List(IsTyped(a2, IntegerType))) =>
              Times(a1, a2)
            case (IsTyped(a1, IntegerType), "%", List(IsTyped(a2, IntegerType))) =>
              Remainder(a1, a2)
            case (IsTyped(a1, IntegerType), "mod", List(IsTyped(a2, IntegerType))) =>
              Modulo(a1, a2)
            case (IsTyped(a1, IntegerType), "/", List(IsTyped(a2, IntegerType))) =>
              Division(a1, a2)
            case (IsTyped(a1, IntegerType), ">", List(IsTyped(a2, IntegerType))) =>
              GreaterThan(a1, a2)
            case (IsTyped(a1, IntegerType), ">=", List(IsTyped(a2, IntegerType))) =>
              GreaterEquals(a1, a2)
            case (IsTyped(a1, IntegerType), "<", List(IsTyped(a2, IntegerType))) =>
              LessThan(a1, a2)
            case (IsTyped(a1, IntegerType), "<=", List(IsTyped(a2, IntegerType))) =>
              LessEquals(a1, a2)

            //Real methods
            case (IsTyped(a1, RealType), "+", List(IsTyped(a2, RealType))) =>
              RealPlus(a1, a2)
            case (IsTyped(a1, RealType), "-", List(IsTyped(a2, RealType))) =>
              RealMinus(a1, a2)
            case (IsTyped(a1, RealType), "*", List(IsTyped(a2, RealType))) =>
              RealTimes(a1, a2)
            case (IsTyped(a1, RealType), "/", List(IsTyped(a2, RealType))) =>
              RealDivision(a1, a2)
            case (IsTyped(a1, RealType), ">", List(IsTyped(a2, RealType))) =>
              GreaterThan(a1, a2)
            case (IsTyped(a1, RealType), ">=", List(IsTyped(a2, RealType))) =>
              GreaterEquals(a1, a2)
            case (IsTyped(a1, RealType), "<", List(IsTyped(a2, RealType))) =>
              LessThan(a1, a2)
            case (IsTyped(a1, RealType), "<=", List(IsTyped(a2, RealType))) =>
              LessEquals(a1, a2)

            // Int methods
            case (IsTyped(a1, Int32Type), "+", List(IsTyped(a2, Int32Type))) =>
              BVPlus(a1, a2)
            case (IsTyped(a1, Int32Type), "-", List(IsTyped(a2, Int32Type))) =>
              BVMinus(a1, a2)
            case (IsTyped(a1, Int32Type), "*", List(IsTyped(a2, Int32Type))) =>
              BVTimes(a1, a2)
            case (IsTyped(a1, Int32Type), "%", List(IsTyped(a2, Int32Type))) =>
              BVRemainder(a1, a2)
            case (IsTyped(a1, Int32Type), "/", List(IsTyped(a2, Int32Type))) =>
              BVDivision(a1, a2)

            case (IsTyped(a1, Int32Type), "|", List(IsTyped(a2, Int32Type))) =>
              BVOr(a1, a2)
            case (IsTyped(a1, Int32Type), "&", List(IsTyped(a2, Int32Type))) =>
              BVAnd(a1, a2)
            case (IsTyped(a1, Int32Type), "^", List(IsTyped(a2, Int32Type))) =>
              BVXOr(a1, a2)
            case (IsTyped(a1, Int32Type), "<<", List(IsTyped(a2, Int32Type))) =>
              BVShiftLeft(a1, a2)
            case (IsTyped(a1, Int32Type), ">>", List(IsTyped(a2, Int32Type))) =>
              BVAShiftRight(a1, a2)
            case (IsTyped(a1, Int32Type), ">>>", List(IsTyped(a2, Int32Type))) =>
              BVLShiftRight(a1, a2)

            case (IsTyped(a1, Int32Type), ">", List(IsTyped(a2, Int32Type))) =>
              GreaterThan(a1, a2)
            case (IsTyped(a1, Int32Type), ">=", List(IsTyped(a2, Int32Type))) =>
              GreaterEquals(a1, a2)
            case (IsTyped(a1, Int32Type), "<", List(IsTyped(a2, Int32Type))) =>
              LessThan(a1, a2)
            case (IsTyped(a1, Int32Type), "<=", List(IsTyped(a2, Int32Type))) =>
              LessEquals(a1, a2)

            // Boolean methods
            case (IsTyped(a1, BooleanType), "&&", List(IsTyped(a2, BooleanType))) =>
              and(a1, a2)

            case (IsTyped(a1, BooleanType), "||", List(IsTyped(a2, BooleanType))) =>
              or(a1, a2)

            // Set methods
            case (IsTyped(a1, SetType(b1)), "size", Nil) =>
              SetCardinality(a1)

            //case (IsTyped(a1, SetType(b1)), "min", Nil) =>
            //  SetMin(a1)

            //case (IsTyped(a1, SetType(b1)), "max", Nil) =>
            //  SetMax(a1)

            case (IsTyped(a1, SetType(b1)), "++", List(IsTyped(a2, SetType(b2))))  if b1 == b2 =>
              SetUnion(a1, a2)

            case (IsTyped(a1, SetType(b1)), "&", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SetIntersection(a1, a2)

            case (IsTyped(a1, SetType(b1)), "subsetOf", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SubsetOf(a1, a2)

            case (IsTyped(a1, SetType(b1)), "--", List(IsTyped(a2, SetType(b2)))) if b1 == b2 =>
              SetDifference(a1, a2)

            case (IsTyped(a1, SetType(b1)), "contains", List(a2)) =>
              ElementOfSet(a2, a1)

            case (IsTyped(a1, SetType(b1)), "isEmpty", List()) =>
              Equals(a1, FiniteSet(Set(), b1))

            // Array methods
            case (IsTyped(a1, ArrayType(vt)), "apply", List(a2)) =>
              ArraySelect(a1, a2)

            case (IsTyped(a1, at: ArrayType), "length", Nil) =>
              ArrayLength(a1)

            case (IsTyped(a1, at: ArrayType), "updated", List(k, v)) =>
              ArrayUpdated(a1, k, v)

            case (IsTyped(a1, at: ArrayType), "clone", Nil) =>
              a1


            // Map methods
            case (IsTyped(a1, MapType(_, vt)), "apply", List(a2)) =>
              MapApply(a1, a2)

            case (IsTyped(a1, MapType(_, vt)), "get", List(a2)) =>
              val someClass = CaseClassType(libraryCaseClass(sym.pos, "leon.lang.Some"), Seq(vt))
              val noneClass = CaseClassType(libraryCaseClass(sym.pos, "leon.lang.None"), Seq(vt))

              IfExpr(MapIsDefinedAt(a1, a2).setPos(current.pos),
                CaseClass(someClass, Seq(MapApply(a1, a2).setPos(current.pos))).setPos(current.pos),
                CaseClass(noneClass, Seq()).setPos(current.pos))

            case (IsTyped(a1, MapType(_, vt)), "getOrElse", List(a2, a3)) =>
              IfExpr(MapIsDefinedAt(a1, a2).setPos(current.pos),
                MapApply(a1, a2).setPos(current.pos),
                a3)

            case (IsTyped(a1, mt: MapType), "isDefinedAt", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "contains", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "updated", List(k, v)) =>
              MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))

            case (IsTyped(a1, mt: MapType), "+", List(k, v)) =>
              MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))

            case (IsTyped(a1, mt: MapType), "+", List(IsTyped(kv, TupleType(List(_, _))))) =>
              kv match {
                case Tuple(List(k, v)) =>
                  MapUnion(a1, FiniteMap(Map(k -> v), mt.from, mt.to))
                case kv =>
                  MapUnion(a1, FiniteMap(Map(TupleSelect(kv, 1) -> TupleSelect(kv, 2)), mt.from, mt.to))
              }

            case (IsTyped(a1, mt1: MapType), "++", List(IsTyped(a2, mt2: MapType)))  if mt1 == mt2 =>
              MapUnion(a1, a2)

            // Char operations
            case (IsTyped(a1, CharType), ">", List(IsTyped(a2, CharType))) =>
              GreaterThan(a1, a2)

            case (IsTyped(a1, CharType), ">=", List(IsTyped(a2, CharType))) =>
              GreaterEquals(a1, a2)

            case (IsTyped(a1, CharType), "<", List(IsTyped(a2, CharType))) =>
              LessThan(a1, a2)

            case (IsTyped(a1, CharType), "<=", List(IsTyped(a2, CharType))) =>
              LessEquals(a1, a2)

            case (a1, name, a2) =>
              val typea1 = a1.getType
              val typea2 = a2.map(_.getType).mkString(",")
              val sa2 = a2.mkString(",")
              try {
              println(Thread.currentThread().getStackTrace.take(5).mkString("\n"))
              } catch { case e: Throwable => }
              outOfSubsetError(tr, "Unknown call to " + name + s" on $a1 ($typea1) with arguments $sa2 of type $typea2")
          }

        // default behaviour is to complain :)
        case _ =>
          outOfSubsetError(tr, "Could not extract as PureScala (Scala tree of type "+tr.getClass+")")
      }

      res.setPos(current.pos)

      rest match {
        case Some(r) =>
          LeonBlock(Seq(res), extractTree(r))
        case None =>
          res
      }
    }

    private def extractType(t: Tree)(implicit dctx: DefContext): LeonType = {
      extractType(t.tpe)(dctx, t.pos)
    }

    private def extractType(tpt: Type)(implicit dctx: DefContext, pos: Position): LeonType = tpt match {
      case tpe if tpe == CharClass.tpe =>
        CharType

      case tpe if tpe == IntClass.tpe =>
        Int32Type

      case tpe if tpe == BooleanClass.tpe =>
        BooleanType

      case tpe if tpe == UnitClass.tpe =>
        UnitType

      case tpe if tpe == NothingClass.tpe =>
        Untyped

      case ct: ConstantType =>
        extractType(ct.value.tpe)

      case TypeRef(_, sym, _) if isBigIntSym(sym) =>
        IntegerType

      case TypeRef(_, sym, _) if isRealSym(sym) =>
        RealType
      
      case TypeRef(_, sym, _) if isStringSym(sym) =>
        StringType

      case TypeRef(_, sym, btt :: Nil) if isScalaSetSym(sym) =>
        outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")

      case TypeRef(_, sym, List(a,b)) if isScalaMapSym(sym) =>
        outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

      case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
        SetType(extractType(btt))

      case TypeRef(_, sym, List(ftt,ttt)) if isMapSym(sym) =>
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

      // TODO: What about Function0?
      case TypeRef(_, sym, subs) if subs.size > 1 && isFunction(sym, subs.size - 1) =>
        val from = subs.init
        val to   = subs.last
        FunctionType(from map extractType, extractType(to))

      case TypeRef(_, sym, tps) if isByNameSym(sym) =>
        extractType(tps.head)

      case tr @ TypeRef(_, sym, tps) =>
        val leontps = tps.map(extractType)

        if (sym.isAbstractType) {
          if(dctx.tparams contains sym) {
            dctx.tparams(sym)
          } else {
            outOfSubsetError(pos, "Unknown type parameter "+sym)
          }
        } else {
          getClassType(sym, leontps)
        }

      case tt: ThisType =>
        val cd = getClassDef(tt.sym, pos)
        cd.typed // Typed using own's type parameters

      case SingleType(_, sym) =>
        getClassType(sym.moduleClass, Nil)

      case RefinedType(parents, defs) if defs.isEmpty =>
        /**
         * For cases like if(a) e1 else e2 where
         *   e1 <: C1,
         *   e2 <: C2,
         *   with C1,C2 <: C
         *
         * Scala might infer a type for C such as: Product with Serializable with C
         * we generalize to the first known type, e.g. C.
         */
        parents.flatMap { ptpe =>
          try {
            Some(extractType(ptpe))
          } catch {
            case e: ImpureCodeEncounteredException =>
              None
        }}.headOption match {
          case Some(tpe) =>
            tpe

          case None =>
            outOfSubsetError(tpt.typeSymbol.pos, "Could not extract refined type as PureScala: "+tpt+" ("+tpt.getClass+")")
        }

      case AnnotatedType(_, tpe) => extractType(tpe)

      case _ =>
        if (tpt ne null) {
          outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
        } else {
          outOfSubsetError(NoPosition, "Tree with null-pointer as type found")
        }
    }

    private def getClassType(sym: Symbol, tps: List[LeonType])(implicit dctx: DefContext) = {
      if (seenClasses contains sym) {
        getClassDef(sym, NoPosition).typed(tps)
      } else {
        outOfSubsetError(NoPosition, "Unknown class "+sym.fullName)
      }
    }

    private def getReturnedExpr(expr: LeonExpr): Seq[LeonExpr] = expr match {
      case Let(_, _, rest) => getReturnedExpr(rest)
      case LetVar(_, _, rest) => getReturnedExpr(rest)
      case LeonBlock(_, rest) => getReturnedExpr(rest)
      case IfExpr(_, thenn, elze) => getReturnedExpr(thenn) ++ getReturnedExpr(elze)
      case MatchExpr(_, cses) => cses.flatMap{ cse => getReturnedExpr(cse.rhs) }
      case _ => Seq(expr)
    }

    def getOwner(exprs: Seq[LeonExpr]): Option[Option[FunDef]] = {
      val exprOwners: Seq[Option[Option[FunDef]]] = exprs.map {
        case Variable(id) =>
          owners.get(id)
        case _ =>
          None
      }

      if(exprOwners.contains(None))
        None
      else if(exprOwners.contains(Some(None)))
        Some(None)
      else if(exprOwners.exists(o1 => exprOwners.exists(o2 => o1 != o2)))
        Some(None)
      else
        exprOwners.head
    }

    def getOwner(expr: LeonExpr): Option[Option[FunDef]] = getOwner(getReturnedExpr(expr))
  }

  def containsLetDef(expr: LeonExpr): Boolean = {
    exists {
      case (l: LetDef) => true
      case _ => false
    }(expr)
  }
}
