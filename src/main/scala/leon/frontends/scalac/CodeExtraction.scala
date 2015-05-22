/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package frontends.scalac

import scala.reflect.internal.util._

import scala.language.implicitConversions

import purescala._
import purescala.Definitions.{
  ClassDef  => LeonClassDef, 
  ModuleDef => LeonModuleDef, 
  ValDef    => LeonValDef, 
  Import    => LeonImport,
  _
}
import purescala.Expressions.{Expr => LeonExpr, This => LeonThis, _}
import purescala.Types.{TypeTree => LeonType, _}
import purescala.Common._
import purescala.Extractors._
import purescala.Constructors._
import purescala.ExprOps._
import purescala.TypeOps._
import purescala.DefOps.packageOf
import xlang.Expressions.{Block => LeonBlock, _}
import xlang.ExprOps._

import utils.{DefinedPosition, Position => LeonPosition, OffsetPosition => LeonOffsetPosition, RangePosition => LeonRangePosition}

trait CodeExtraction extends ASTExtractors {
  self: LeonExtraction =>

  import global._
  import global.definitions._
  import StructuralExtractors._
  import ExpressionExtractors._
  import scala.collection.immutable.Set

  val reporter = self.ctx.reporter

  def annotationsOf(s: Symbol): Set[String] = {
    val actualSymbol = s.accessedOrSelf

    (for(a <- actualSymbol.annotations ++ actualSymbol.owner.annotations) yield {
      val name = a.atp.safeToString.replaceAll("\\.package\\.", ".")
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
  case class TempModule(name : Identifier, trees : List[Tree], isStandalone : Boolean)
  case class TempUnit(
    name : String, 
    pack : PackageRef, 
    modules : List[TempModule], 
    imports : List[Import],
    isPrintable : Boolean
  ) 
    
  class Extraction(units: List[CompilationUnit]) {
        
    private var currentFunDef: FunDef = null

    //This is a bit misleading, if an expr is not mapped then it has no owner, if it is mapped to None it means
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
    def toPureScalaType(tpt: Type)(implicit dctx: DefContext, pos: Position): LeonType = {
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
        mutableVars: Map[Symbol, () => LeonExpr] = Map()
      ) {

      def union(that: DefContext) = {
        copy(this.tparams ++ that.tparams,
             this.vars ++ that.vars,
             this.mutableVars ++ that.mutableVars)
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

    def isIgnored(s: Symbol) = {
      (annotationsOf(s) contains "ignore") || s.fullName.toString.endsWith(".main")
    }
    
    def extractUnits: List[UnitDef] = {
      try {
        def isLib(u : CompilationUnit) = Build.libFiles contains u.source.file.absolute.path
        
        val templates: List[TempUnit] = units.reverseMap { u => u.body match {

          // Unit with a single package object
          case PackageDef(refTree, List(PackageDef(inner, List(ExObjectDef(n, templ))))) if n == "package" =>
            // File name without extension
            val unitName = extractPackageRef(inner).mkString("$") + "$package"
            val id = FreshIdentifier(unitName + "$standalone")
            TempUnit(unitName,
              extractPackageRef(refTree) ++ extractPackageRef(inner),
              List(TempModule(id, templ.body, true)),
              imports.getOrElse(refTree, Nil),
              !isLib(u)
            )

          case pd@PackageDef(refTree, lst) =>

            var standaloneDefs = List[Tree]()

            val modules = lst.flatMap {

              case t if isIgnored(t.symbol) =>
                None

              case po@ExObjectDef(n, templ) if n == "package" =>
                outOfSubsetError(po, "No other definitions are allowed in a file with a package object.")

              case ExObjectDef(n, templ) if n != "package" =>
                Some(TempModule(FreshIdentifier(n), templ.body, false))

              /*
              case d @ ExCompanionObjectSynthetic(_, sym, templ) =>
                // Find default param. implementations
                templ.body foreach {
                  case ExDefaultValueFunction(sym, _, _, _, owner, index, _) =>
                    val namePieces = sym.toString.reverse.split("\\$", 3).reverse map { _.reverse }
                    assert(namePieces.length == 3 && namePieces(0)== "$lessinit$greater" && namePieces(1) == "default") // FIXME : maybe $lessinit$greater?
                    val index = namePieces(2).toInt
                    val theParam = sym.companionClass.paramss.head(index - 1)
                    paramsToDefaultValues += theParam -> body
                  case _ =>
                }
                None
              */

              case d@ExAbstractClass(_, _, _) =>
                standaloneDefs ::= d
                None

              case d@ExCaseClass(_, _, _, _) =>
                standaloneDefs ::= d
                None

              case d@ExCaseClassSyntheticJunk() =>
                None

              case cd: ClassDef =>
                outOfSubsetError(cd, "Found class that is not an abstract class nor a case class")
                None

              case other =>
                outOfSubsetError(other, "Expected: top-level object/class.")
                None
            }

            // File name without extension
            val unitName = u.source.file.name.replaceFirst("[.][^.]+$", "")
            val finalModules =
              if (standaloneDefs.isEmpty) modules
              else {
                val id = FreshIdentifier(unitName + "$standalone")
                TempModule(id, standaloneDefs, true) :: modules
              }

            TempUnit(unitName,
              extractPackageRef(refTree),
              finalModules,
              imports.getOrElse(refTree, Nil),
              !isLib(u)
            )
        }}

        // Phase 1, we detect objects/classes/types
        for (temp <- templates; mod <- temp.modules) collectClassSymbols(mod.trees)
                
        // Phase 2, we collect functions signatures
        for (temp <- templates; mod <- temp.modules) collectFunSigs(mod.trees)

        // Phase 3, we collect classes/types' definitions
        for (temp <- templates; mod <- temp.modules) extractClassDefs(mod.trees)

        // Phase 4, we collect methods' definitions
        for (temp <- templates; mod <- temp.modules) extractMethodDefs(mod.trees)

        // Phase 5, we collect function definitions
        for (temp <- templates; mod <- temp.modules) extractFunDefs(mod.trees)

        // Phase 6, we create modules and extract bodies
        for (temp <- templates; mod <- temp.modules) extractObjectDef(mod.name, mod.trees, mod.isStandalone)
        
        // Phase 7, we wrap modules in units
        // We first form the units without valid imports
        val withoutImports = for (TempUnit(name,pack,mods,imps,isPrintable) <- templates) yield { 
          ( UnitDef(
              FreshIdentifier(name), 
              for( TempModule(nm,_,_) <- mods) yield objects2Objects(nm), 
              pack, Nil, isPrintable
            )
          , imps 
          )
        }
        
        // Just doing this so everything is in the same program and searches work properly
        val _ = Program(FreshIdentifier("__program"), withoutImports map { _._1 })

        // With the aid of formed units, we extract the correct imports
        val objPerPack = objects2Objects map { _._2 } groupBy { packageOf(_)}
        withoutImports map { case (u, imps) =>
          u.copy(imports = {
            // Extract imports from source
            val extracted = imps flatMap { extractImport(_, u,withoutImports map { _._1}) }
            // Add extra imports for contents of standalone objects
            val packs = u.pack :: extracted. collect { case PackageImport(pack) => pack } 
            val additional = objPerPack. collect { 
              case (p,obs) if packs contains p =>
                obs filter { _.isStandalone} map WildcardImport
            }.flatten
            extracted ++ additional
          })
        }

      } catch {
        case icee: ImpureCodeEncounteredException =>
          icee.emit()
          Nil
      }

    }
      
    
    
    private def getSelectChain(e : Tree) : List[String] = {
      def rec (e : Tree) : List[Name] = e match {
        case Select(q, name) => name :: rec(q)
        case Ident(name) => List(name)
        case EmptyTree => List()
        case _ => ctx.reporter.internalError("getSelectChain: unexpected Tree:\n" + e.toString)
      } 
      rec(e).reverseMap(_.toString)
    }
    
    private def extractPackageRef(refPath : RefTree) : PackageRef =       
      (getSelectChain(refPath.qualifier) :+ refPath.name.toString) match {
        // Make sure to drop "<empty>" package
        case List("<empty>") => List()
        case other => other
      }
    
    private def extractImport(i : Import, current : UnitDef, units : List[UnitDef]) : Seq[ LeonImport ] = i match { case Import(expr, sels) => 
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
          
        val theDef = searchByFullNameRelative(thePath mkString ".", current, reliableVisibility = false)
        
        (isWild, theDef) match {
          case (true, Some(df)) => Some(WildcardImport(df))
          case (false,Some(df)) => Some(SingleImport(df))
          case (true, None)     => Some(PackageImport(thePath))
          case (false,None)     => None // import comes from a Scala library or something... 
        }
      }
    }

    private var seenClasses = Map[Symbol, (Seq[(Symbol, ValDef)], Template)]()
    private var classesToClasses  = Map[Symbol, LeonClassDef]()

    def oracleType(pos: Position, tpe: LeonType) = {
      classesToClasses.find {
        case (sym, cl) => sym.fullName.toString == "leon.lang.synthesis.Oracle"
      } match {
        case Some((_, cd)) =>
          classDefToClassType(cd, List(tpe))
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

    private def collectClassSymbols(defs: List[Tree]) {
      // We collect all defined classes
      for (t <- defs) t match {
        case t if isIgnored(t.symbol) =>
          // ignore

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
        case t if isIgnored(t.symbol) =>
          // ignore

        case ExAbstractClass(o2, sym, _) =>
          getClassDef(sym, t.pos)

        case ExCaseClass(o2, sym, args, _) =>
          getClassDef(sym, t.pos)

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
            if (sym.name.toString == "synthesis") {
              new Exception().printStackTrace()
            }
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
              val newTps = tps.map(extractType(_)(defCtx, sym.pos))
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

        val fields = args.map { case (symbol, t) =>
          val tpt = t.tpt
          val tpe = toPureScalaType(tpt.tpe)(defCtx, sym.pos)
          LeonValDef(FreshIdentifier(symbol.name.toString, tpe).setPos(t.pos)).setPos(t.pos)
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

      // We collect the methods and fields 
      for (d <- tmpl.body) d match {
        case EmptyTree =>
          // ignore

        case t if isIgnored(t.symbol) =>
          // ignore

        // Normal methods
        case t @ ExFunctionDef(fsym, _, _, _, _) =>
          if (parent.isDefined) {
            outOfSubsetError(t, "Only hierarchy roots can define methods")
          }
          val fd = defineFunDef(fsym)(defCtx)

          isMethod += fsym
          methodToClass += fd -> cd

          cd.registerMethod(fd)

        // Default values for parameters
        case t@ ExDefaultValueFunction(fsym, _, _, _, owner, index, _) =>          
          val fd = defineFunDef(fsym)(defCtx)
          fd.addAnnotation("synthetic")
                    
          isMethod += fsym
          methodToClass += fd -> cd

          cd.registerMethod(fd)       
          val matcher : PartialFunction[Tree, Symbol] = { 
            case ExFunctionDef(ownerSym, _ ,_ ,_, _) if ownerSym.name.toString == owner => ownerSym 
          } 
          registerDefaultMethod(tmpl.body, matcher, index, fd )
                   
          
        // Lazy fields
        case t @ ExLazyAccessorFunction(fsym, _, _)  =>
          if (parent.isDefined) {
            outOfSubsetError(t, "Only hierarchy roots can define lazy fields") 
          }
          val fd = defineFieldFunDef(fsym, true)(defCtx)

          isMethod += fsym
          methodToClass += fd -> cd

          cd.registerMethod(fd)
        
        // normal fields
        case t @ ExFieldDef(fsym, _, _) => 
          // we will be using the accessor method of this field everywhere 
          val fsymAsMethod = fsym
          if (parent.isDefined) {
            outOfSubsetError(t, "Only hierarchy roots can define fields") 
          }
          val fd = defineFieldFunDef(fsymAsMethod, false)(defCtx)

          isMethod += fsymAsMethod
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

      val nctx = dctx.copy(tparams = dctx.tparams ++ tparams.toMap)

      val newParams = sym.info.paramss.flatten.map{ sym =>
        val ptpe = toPureScalaType(sym.tpe)(nctx, sym.pos)
        val newID = FreshIdentifier(sym.name.toString, ptpe).setPos(sym.pos)
        owners += (newID -> None)
        LeonValDef(newID).setPos(sym.pos)
      }

      val tparamsDef = tparams.map(t => TypeParameterDef(t._2))

      val returnType = toPureScalaType(sym.info.finalResultType)(nctx, sym.pos)

      val name = sym.name.toString

      val fd = new FunDef(FreshIdentifier(name).setPos(sym.pos), tparamsDef, returnType, newParams, DefType.MethodDef)

      fd.setPos(sym.pos)

      fd.addAnnotation(annotationsOf(sym).toSeq : _*)

      defsToDefs += sym -> fd

      fd
    }

    private def defineFieldFunDef(sym : Symbol, isLazy : Boolean)(implicit dctx : DefContext) : FunDef = {

      val nctx = dctx.copy(tparams = dctx.tparams)

      val returnType = toPureScalaType(sym.info.finalResultType)(nctx, sym.pos)

      val name = sym.name.toString

      val fieldType = if (isLazy) DefType.LazyFieldDef else DefType.StrictFieldDef
      
      val fd = new FunDef(FreshIdentifier(name).setPos(sym.pos), Seq(), returnType, Seq(), fieldType)

      fd.setPos(sym.pos)

      fd.addAnnotation(annotationsOf(sym).toSeq : _*)
      
      defsToDefs += sym -> fd

      fd
    }
    
    
    
    private def collectFunSigs(defs: List[Tree]) = {
      // We collect defined function bodies
      for (d <- defs) d match {
        case t if isIgnored(t.symbol) =>
          //ignore

        case ExFunctionDef(sym, _, _, _, _) =>
          defineFunDef(sym)(DefContext())

        case t @ ExDefaultValueFunction(sym, _, _, _, owner, index, _) => { 
          
          val fd = defineFunDef(sym)(DefContext())
          fd.addAnnotation("synthetic")
          val matcher : PartialFunction[Tree, Symbol] = { 
            case ExFunctionDef(ownerSym, _ ,_ ,_, _) if ownerSym.name.toString == owner => ownerSym 
          } 
          registerDefaultMethod(defs, matcher, index, fd)
           
        }
        case ExLazyAccessorFunction(sym, _, _)  =>
          defineFieldFunDef(sym,true)(DefContext())
          
        case ExFieldDef(sym, _, _) =>
          defineFieldFunDef(sym, false)(DefContext())
          
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
      for (d <- defs) d match {
        case t if isIgnored(t.symbol) =>
          // ignore

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
        case t if isIgnored(t.symbol) =>
          // ignore

         
        case ExFunctionDef(sym, tparams, params, _, body) =>
          // Methods
          val fd = defsToDefs(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          extractFunBody(fd, params, body)(DefContext(tparamsMap))

        case ExDefaultValueFunction(sym, tparams, params, _ ,_ , _, body) =>
          // Default value functions
          val fd = defsToDefs(sym)

          val tparamsMap = (tparams zip fd.tparams.map(_.tp)).toMap

          extractFunBody(fd, params, body)(DefContext(tparamsMap))
          
        case ExLazyAccessorFunction(sym, _, body)  =>
          // Lazy vals
          val fd = defsToDefs(sym)
          extractFunBody(fd, Seq(), body)(DefContext())

        case ExFieldDef(sym, tpe, body) =>
          // Normal vals
          val fd = defsToDefs(sym)
          extractFunBody(fd, Seq(), body)(DefContext())
          
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

    var objects2Objects = Map[Identifier, LeonModuleDef]()
    
    private def extractObjectDef(id : Identifier, defs: List[Tree], isStandalone : Boolean) {

      val newDefs = defs.flatMap {
        case t if isIgnored(t.symbol) =>
          None

        case ExAbstractClass(o2, sym, _) =>
          Some(classesToClasses(sym))

        case ExCaseClass(o2, sym, args, _) =>
          Some(classesToClasses(sym))

        // Taking accessor functions will duplicate work for strict fields, but we need them in case of lazy fields
        case ExFunctionDef(sym, tparams, params, _, body) =>
          Some(defsToDefs(sym))
        case ExDefaultValueFunction(sym, _, _, _, _, _, _) =>
          Some(defsToDefs(sym))
        case ExLazyAccessorFunction(sym, _, _) =>
          Some(defsToDefs(sym))
        case ExFieldDef(sym, _, _) =>
          Some(defsToDefs(sym))

        case _ =>
          None
      }

      // We check nothing else is polluting the object
      for (t <- defs) t match {
        case ExCaseClassSyntheticJunk() =>
        case ExAbstractClass(_,_,_) =>
        case ExCaseClass(_,_,_,_) =>
        case ExConstructorDef() =>
        case ExFunctionDef(_, _, _, _, _) =>
        case ExLazyAccessorFunction(_, _, _) =>
        case ExDefaultValueFunction(_, _, _, _, _, _, _ ) =>
        case ExFieldDef(_,_,_) =>
        case ExLazyFieldDef() => 
        case ExFieldAccessorFunction() => 
        case d if isIgnored(d.symbol) || (d.symbol.isImplicit && d.symbol.isSynthetic) =>
        case tree =>
          println(tree)
          outOfSubsetError(tree, "Don't know what to do with this. Not purescala?");
      }

      objects2Objects += id -> LeonModuleDef(id, newDefs, isStandalone)
    }


    private def extractFunBody(funDef: FunDef, params: Seq[ValDef], body0 : Tree)(implicit dctx: DefContext): FunDef = {
      currentFunDef = funDef
      
      // Find defining function for params with default value
      for ((s,vd) <- params zip funDef.params) {
        vd.defaultValue = paramsToDefaultValues.get(s.symbol) 
      }
      
      val newVars = for ((s, vd) <- params zip funDef.params) yield {
        s.symbol -> (() => Variable(vd.id))
      }

      val fctx = dctx.withNewVars(newVars)

      // If this is a lazy field definition, drop the assignment/ accessing
      val body = 
        if (funDef.defType == DefType.LazyFieldDef) { body0 match {
          case Block(List(Assign(_, realBody)),_ ) => realBody
          case _ => outOfSubsetError(body0, "Wrong form of lazy accessor")
        }} else body0

      val finalBody = try {
        flattenBlocks(extractTree(body)(fctx)) match {
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
            reporter.warning(funDef.getPos, "Function "+funDef.id.name+" is not fully unavailable to Leon.")
          }

          funDef.addAnnotation("abstract")
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
        val newID = FreshIdentifier(name.toString, extractType(tpt)).setPos(b.pos).setOwner(currentFunDef)
        val pctx = dctx.withNewVar(b.symbol -> (() => Variable(newID)))
        extractPattern(t, Some(newID))(pctx)

      case b @ Bind(name, pat) =>
        val newID = FreshIdentifier(name.toString, extractType(b)).setPos(b.pos).setOwner(currentFunDef)
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

      case s @ Select(_, b) if s.tpe.typeSymbol.isCase  =>
        // case Obj =>
        extractType(s) match {
          case ct: CaseClassType =>
            assert(ct.classDef.fields.size == 0)
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

      case ExInt32Literal(i)   => (LiteralPattern(binder, IntLiteral(i)),     dctx)
      case ExBooleanLiteral(b) => (LiteralPattern(binder, BooleanLiteral(b)), dctx)
      case ExUnitLiteral()     => (LiteralPattern(binder, UnitLiteral()),     dctx)
      case sLit@ExStringLiteral(s)  =>
        val consClass = libraryCaseClass(sLit.pos, "leon.collection.Cons")
        val nilClass = libraryCaseClass(sLit.pos, "leon.collection.Nil")
        val nil = CaseClassPattern(None, CaseClassType(nilClass, Seq(CharType)), Seq())
        val consType = CaseClassType(consClass, Seq(CharType))
        def mkCons(hd: Pattern, tl: Pattern) = CaseClassPattern(None, consType, Seq(hd,tl))
        val chars = s.toCharArray//.asInstanceOf[Seq[Char]]
        def charPat(ch : Char) = LiteralPattern(None, CharLiteral(ch))
        (chars.foldRight(nil)( (ch: Char, p : Pattern) => mkCons( charPat(ch), p)), dctx)

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
        case Block(Nil, last) =>
          (last, None)
        case e =>
          (e, None)
      }

      var rest = tmpRest

      val res = current match {
        case ExEnsuredExpression(body, contract) =>
          val post = extractTree(contract)

          val b = extractTree(body)

          val closure = post.getType match {
            case BooleanType =>
              val resId = FreshIdentifier("res", BooleanType).setPos(post).setOwner(currentFunDef)
              Lambda(Seq(LeonValDef(resId)), post).setPos(post)
            case _ => post
          }

          Ensuring(b, closure)

        case t @ ExHoldsExpression(body) =>
          val resId = FreshIdentifier("holds", BooleanType).setPos(current.pos).setOwner(currentFunDef)
          val post = Lambda(Seq(LeonValDef(resId)), Variable(resId)).setPos(current.pos)

          val b = extractTree(body)

          Ensuring(b, post)

        case ExAssertExpression(contract, oerr) =>
          val const = extractTree(contract)
          val b     = rest.map(extractTree).getOrElse(UnitLiteral())

          rest = None

          Assert(const, oerr, b)

        case ExRequiredExpression(contract) =>
          val pre = extractTree(contract)

          val b = rest.map(extractTree).getOrElse(UnitLiteral())

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
          val newID = FreshIdentifier(vs.name.toString, binderTpe).setOwner(currentFunDef)
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

          val funDefWithBody = extractFunBody(fd, params, b)(newDctx.copy(mutableVars = Map())).setOwner(oldCurrentFunDef)

          currentFunDef = oldCurrentFunDef

          val restTree = rest match {
            case Some(rst) => extractTree(rst)
            case None => UnitLiteral()
          }
          rest = None
          LetDef(funDefWithBody, restTree)

        // FIXME case ExDefaultValueFunction
        
        /**
         * XLang Extractors
         */

        case ExVarDef(vs, tpt, bdy) => {
          val binderTpe = extractType(tpt)
          val newID = FreshIdentifier(vs.name.toString, binderTpe).setOwner(currentFunDef)
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

        case ExBigIntLiteral(n: Literal) => {
          InfiniteIntegerLiteral(BigInt(n.value.stringValue))
        }
        case ExBigIntLiteral(n) => outOfSubsetError(tr, "Non-literal BigInt constructor")

        case ExIntToBigInt(tree) => {
          val rec = extractTree(tree)
          rec match {
            case IntLiteral(n) =>
              InfiniteIntegerLiteral(BigInt(n))
            case _ => 
              outOfSubsetError(tr, "Conversion from Int to BigInt")
          }
        }

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

        case hole @ ExHoleExpression(tpt, exprs) =>
          Hole(extractType(tpt), exprs.map(extractTree))

        case ops @ ExWithOracleExpression(oracles, body) =>
          val newOracles = oracles map { case (tpt, sym) =>
            val aTpe  = extractType(tpt)
            val oTpe  = oracleType(ops.pos, aTpe)
            val newID = FreshIdentifier(sym.name.toString, oTpe).setOwner(currentFunDef)
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

        case f @ ExForallExpression(args, body) =>
          val vds = args map { case (tpt, sym) =>
            val aTpe = extractType(tpt)
            val newID = FreshIdentifier(sym.name.toString, aTpe)
            owners += (newID -> None)
            LeonValDef(newID)
          }

          val newVars = (args zip vds) map { case ((_, sym), vd) =>
            sym -> (() => vd.toVariable)
          }

          val exBody = extractTree(body)(dctx.withNewVars(newVars))

          Forall(vds, exBody)

        case ExFiniteMap(tptFrom, tptTo, args) =>
          val singletons: Seq[(LeonExpr, LeonExpr)] = args.collect {
            case ExTuple(tpes, trees) if trees.size == 2 =>
              (extractTree(trees(0)), extractTree(trees(1)))
          }

          if (singletons.size != args.size) {
            outOfSubsetError(tr, "Some map elements could not be extracted as Tuple2")
          }

          finiteMap(singletons, extractType(tptFrom), extractType(tptTo))

        case ExFiniteSet(tpt, args) =>
          finiteSet(args.map(extractTree).toSet, extractType(tpt))

        case ExCaseClassConstruction(tpt, args) =>
          extractType(tpt) match {
            case cct: CaseClassType =>
              CaseClass(cct, args.map(extractTree))

            case _ =>
              outOfSubsetError(tr, "Construction of a non-case class.")

          }

        case ExNot(e)              => Not(extractTree(e))
        case ExUMinus(e)           => UMinus(extractTree(e))
        case ExBVUMinus(e)         => BVUMinus(extractTree(e))
        case ExBVNot(e)            => BVNot(extractTree(e))

        case ExNotEquals(l, r) => {
          val rl = extractTree(l)
          val rr = extractTree(r)

          (rl, rr) match {
            case (IsTyped(_, rt), IsTyped(_, lt)) if isSubtypeOf(rt, lt) || isSubtypeOf(lt, rt) =>
              Not(Equals(rl, rr))

            case (IntLiteral(v), IsTyped(_, IntegerType)) =>
              Not(Equals(InfiniteIntegerLiteral(v), rr))

            case (IsTyped(_, IntegerType), IntLiteral(v)) =>
              Not(Equals(rl, InfiniteIntegerLiteral(v)))

            case (IsTyped(_, rt), IsTyped(_, lt)) =>
              outOfSubsetError(tr, "Invalid comparison: (_: "+rt+") != (_: "+lt+")")
          }
        }

        case ExEquals(l, r) =>
          val rl = extractTree(l)
          val rr = extractTree(r)

          (rl, rr) match {
            case (IsTyped(_, rt), IsTyped(_, lt)) if isSubtypeOf(rt, lt) || isSubtypeOf(lt, rt) =>
              Equals(rl, rr)

            case (IntLiteral(v), IsTyped(_, IntegerType)) =>
              Equals(InfiniteIntegerLiteral(v), rr)

            case (IsTyped(_, IntegerType), IntLiteral(v)) =>
              Equals(rl, InfiniteIntegerLiteral(v))

            case (IsTyped(_, rt), IsTyped(_, lt)) =>
              outOfSubsetError(tr, "Invalid comparison: (_: "+rt+") == (_: "+lt+")")
          }

        case ExFiniteMultiset(tt, args) =>
          val underlying = extractType(tt)
          finiteMultiset(args.map(extractTree),underlying)

        case ExEmptyMultiset(tt) =>
          val underlying = extractType(tt)
          EmptyMultiset(underlying)

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

        case ExIsInstanceOf(tt, cc) => {
          val ccRec = extractTree(cc)
          val checkType = extractType(tt)
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
          val chars = s.toList.map(CharLiteral)
          
          val consChar = CaseClassType(libraryCaseClass(str.pos, "leon.collection.Cons"), Seq(CharType))
          val nilChar  = CaseClassType(libraryCaseClass(str.pos, "leon.collection.Nil"),  Seq(CharType))

          val charList = chars.foldRight(CaseClass(nilChar, Seq())) {
            case (c, s) => CaseClass(consChar, Seq(c, s))
          }

          CaseClass(CaseClassType(libraryCaseClass(str.pos, "leon.lang.string.String"), Seq()), Seq(charList))


        case ExImplies(lhs, rhs) =>
          Implies(extractTree(lhs), extractTree(rhs)).setPos(current.pos)

        case c @ ExCall(rec, sym, tps, args) =>
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

              FunctionInvocation(fd.typed(newTps), args)

            case (IsTyped(rec, ct: ClassType), _, args) if isMethod(sym) =>
              val fd = getFunDef(sym, c.pos)
              val cd = methodToClass(fd)

              val newTps = tps.map(t => extractType(t))

              MethodInvocation(rec, cd, fd.typed(newTps), args)

            case (IsTyped(rec, ft: FunctionType), _, args) =>
              application(rec, args)

            case (IsTyped(rec, cct: CaseClassType), name, Nil) if cct.fields.exists(_.id.name == name) =>

              val fieldID = cct.fields.find(_.id.name == name).get.id

              CaseClassSelector(cct, rec, fieldID)

            //BigInt methods
            case (IsTyped(a1, IntegerType), "+", List(IsTyped(a2, IntegerType))) =>
              Plus(a1, a2)
            case (IsTyped(a1, IntegerType), "-", List(IsTyped(a2, IntegerType))) =>
              Minus(a1, a2)
            case (IsTyped(a1, IntegerType), "*", List(IsTyped(a2, IntegerType))) =>
              Times(a1, a2)
            case (IsTyped(a1, IntegerType), "%", List(IsTyped(a2, IntegerType))) =>
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

            // Int methods
            case (IsTyped(a1, Int32Type), "+", List(IsTyped(a2, Int32Type))) =>
              BVPlus(a1, a2)
            case (IsTyped(a1, Int32Type), "-", List(IsTyped(a2, Int32Type))) =>
              BVMinus(a1, a2)
            case (IsTyped(a1, Int32Type), "*", List(IsTyped(a2, Int32Type))) =>
              BVTimes(a1, a2)
            case (IsTyped(a1, Int32Type), "%", List(IsTyped(a2, Int32Type))) =>
              BVModulo(a1, a2)
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
              Equals(a1, finiteSet(Set(), b1))

            // Multiset methods
            case (IsTyped(a1, MultisetType(b1)), "++", List(IsTyped(a2, MultisetType(b2))))  if b1 == b2 =>
              MultisetUnion(a1, a2)

            case (IsTyped(a1, MultisetType(b1)), "&", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetIntersection(a1, a2)

            case (IsTyped(a1, MultisetType(b1)), "--", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetDifference(a1, a2)

            case (IsTyped(a1, MultisetType(b1)), "+++", List(IsTyped(a2, MultisetType(b2)))) if b1 == b2 =>
              MultisetPlus(a1, a2)

            case (IsTyped(_, MultisetType(b1)), "toSet", Nil) =>
              MultisetToSet(rrec)

            // Array methods
            case (IsTyped(a1, ArrayType(vt)), "apply", List(a2)) =>
              ArraySelect(a1, a2)

            case (IsTyped(a1, at: ArrayType), "length", Nil) =>
              ArrayLength(a1)

            case (IsTyped(a1, at: ArrayType), "updated", List(k, v)) =>
              ArrayUpdated(a1, k, v)


            // Map methods
            case (IsTyped(a1, MapType(_, vt)), "apply", List(a2)) =>
              MapGet(a1, a2)

            case (IsTyped(a1, mt: MapType), "isDefinedAt", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "contains", List(a2)) =>
              MapIsDefinedAt(a1, a2)

            case (IsTyped(a1, mt: MapType), "updated", List(k, v)) =>
              MapUnion(a1, NonemptyMap(Seq((k, v))))

            case (IsTyped(a1, mt1: MapType), "++", List(IsTyped(a2, mt2: MapType)))  if mt1 == mt2 =>
              MapUnion(a1, a2)
              
            case (_, name, _) =>
              outOfSubsetError(tr, "Unknown call to "+name)
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

      case TypeRef(_, sym, _) if isBigIntSym(sym) =>
        IntegerType

      case TypeRef(_, sym, btt :: Nil) if isScalaSetSym(sym) =>
        outOfSubsetError(pos, "Scala's Set API is no longer extracted. Make sure you import leon.lang.Set that defines supported Set operations.")

      case TypeRef(_, sym, List(a,b)) if isScalaMapSym(sym) =>
        outOfSubsetError(pos, "Scala's Map API is no longer extracted. Make sure you import leon.lang.Map that defines supported Map operations.")

      case TypeRef(_, sym, btt :: Nil) if isSetSym(sym) =>
        SetType(extractType(btt))

      case TypeRef(_, sym, btt :: Nil) if isMultisetTraitSym(sym) =>
        MultisetType(extractType(btt))

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

      case TypeRef(_, sym, List(f1,to)) if isFunction1(sym) =>
        FunctionType(Seq(extractType(f1)), extractType(to))

      case TypeRef(_, sym, List(f1,f2,to)) if isFunction2(sym) =>
        FunctionType(Seq(extractType(f1),extractType(f2)), extractType(to))

      case TypeRef(_, sym, List(f1,f2,f3,to)) if isFunction3(sym) =>
        FunctionType(Seq(extractType(f1),extractType(f2),extractType(f3)), extractType(to))

      case TypeRef(_, sym, List(f1,f2,f3,f4,to)) if isFunction4(sym) =>
        FunctionType(Seq(extractType(f1),extractType(f2),extractType(f3),extractType(f4)), extractType(to))

      case TypeRef(_, sym, List(f1,f2,f3,f4,f5,to)) if isFunction5(sym) =>
        FunctionType(Seq(extractType(f1),extractType(f2),extractType(f3),extractType(f4),extractType(f5)), extractType(to))

      case TypeRef(_, sym, tps) if isByNameSym(sym) =>
        extractType(tps.head)

      case TypeRef(_, sym, tps) =>
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
        classDefToClassType(cd, cd.tparams.map(_.tp)) // Typed using own's type parameters

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
        outOfSubsetError(tpt.typeSymbol.pos, "Could not extract type as PureScala: "+tpt+" ("+tpt.getClass+")")
    }

    private var unknownsToTP        = Map[Symbol, TypeParameter]()

    private def getClassType(sym: Symbol, tps: List[LeonType])(implicit dctx: DefContext) = {
      if (seenClasses contains sym) {
        classDefToClassType(getClassDef(sym, NoPosition), tps)
      } else {
        outOfSubsetError(NoPosition, "Unknown class "+sym.fullName)
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
