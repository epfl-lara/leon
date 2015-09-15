/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import utils.Library
import Common._
import Expressions._
import ExprOps._
import Types._
import TypeOps._

object Definitions {

  sealed abstract class Definition extends Tree {
    
    val id: Identifier

    def subDefinitions : Seq[Definition]      // The enclosed scopes/definitions by this definition
  
    def containsDef(df: Definition): Boolean = {
      subDefinitions.exists { sd =>
        sd == df || sd.containsDef(df)
      }
    }

    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }

    def writeScalaFile(filename: String, opgm: Option[Program] = None) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this, opgm = opgm))
      out.close()
    }
  }

  /** A ValDef represents a parameter of a [[purescala.Definitions.FunDef function]] or
    * a [[purescala.Definitions.CaseClassDef case class]].
    *
    *  The optional [[tpe]], if present, overrides the type of the underlying Identifier [[id]].
    *  This is useful to instantiate argument types of polymorphic classes. To be consistent,
    *  never use the type of [[id]] directly; use [[ValDef#getType]] instead.
    */
  case class ValDef(id: Identifier, tpe: Option[TypeTree] = None) extends Definition with Typed {
    self: Serializable =>

    val getType = tpe getOrElse id.getType

    var defaultValue : Option[FunDef] = None

    def subDefinitions = Seq()

    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]]
      *
      * Warning: the variable will not have the same type as this ValDef, but currently
      * the Identifier type is enough for all uses in Leon.
      */
    def toVariable : Variable = Variable(id)
  }

  /** A wrapper for a program. For now a program is simply a single object. */
  case class Program(units: List[UnitDef]) extends Definition {
    val id = FreshIdentifier("program")

    lazy val library = Library(this)

    def subDefinitions = units

    def definedFunctions    = units.flatMap(_.definedFunctions)
    def definedClasses      = units.flatMap(_.definedClasses)
    def classHierarchyRoots = units.flatMap(_.classHierarchyRoots)
    def singleCaseClasses   = units.flatMap(_.singleCaseClasses)
    def modules             = {
      units.flatMap(_.defs.collect {
        case md: ModuleDef => md
      })
    }

    lazy val callGraph      = new CallGraph(this)

    def caseClassDef(name: String) = definedClasses.collectFirst {
      case ccd: CaseClassDef if ccd.id.name == name => ccd
    }.getOrElse(throw LeonFatalError("Unknown case class '"+name+"'"))

    def lookupAll(name: String)  = DefOps.searchWithin(name, this)
    def lookup(name: String)     = lookupAll(name).headOption
  }

  object Program {
    lazy val empty: Program = Program(Nil)
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def subDefinitions = Seq()
    def freshen = TypeParameterDef(tp.freshen)
    val id = tp.id
  }
 
  /** A package as a path of names */
  type PackageRef = List[String] 

  case class Import(path: List[String], isWild: Boolean) extends Tree {
    def importedDefs(in: UnitDef)(implicit pgm: Program): Seq[Definition] = {
      val found = DefOps.searchRelative(path.mkString("."), in)
      if (isWild) {
        found.flatMap(_.subDefinitions)
      } else {
        found
      }
    }
  }
  
  case class UnitDef(
    id: Identifier,
    pack : PackageRef,
    imports : Seq[Import],
    defs : Seq[Definition],
    isMainUnit : Boolean // false for libraries/imports
  ) extends Definition {
     
    def subDefinitions = defs
    
    def definedFunctions = defs.flatMap{
      case m: ModuleDef => m.definedFunctions
      case _ => Nil
    }

    def definedClasses = defs.flatMap {
      case c: ClassDef => List(c)
      case m: ModuleDef => m.definedClasses
      case _ => Nil
    }

    def classHierarchyRoots = {
      definedClasses.filter(!_.hasParent)
    }

    // Guarantees that a parent always appears before its children
    def classHierarchies = classHierarchyRoots map { root =>
      root +: root.knownDescendants
    }

    def singleCaseClasses = {
      definedClasses.collect {
        case ccd: CaseClassDef if !ccd.hasParent => ccd
      }
    }

    def modules = defs.collect {
      case md: ModuleDef => md
    }
  }
  
  object UnitDef {
    def apply(id: Identifier, modules : Seq[ModuleDef]) : UnitDef = 
      UnitDef(id,Nil, Nil, modules,true)
  }
  
  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(id: Identifier, defs: Seq[Definition], isPackageObject: Boolean) extends Definition {
    
    def subDefinitions = defs
    
    lazy val definedFunctions : Seq[FunDef] = defs.collect { case fd: FunDef => fd }

    lazy val definedClasses : Seq[ClassDef] = defs.collect { case ctd: ClassDef => ctd }

    lazy val classHierarchyRoots : Seq[ClassDef] = defs.collect {
      case ctd: ClassDef if !ctd.hasParent => ctd
    }

    lazy val algebraicDataTypes : Map[AbstractClassDef, Seq[CaseClassDef]] = defs.collect {
      case c@CaseClassDef(_, _, Some(p), _) => c
    }.groupBy(_.parent.get.classDef)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c @ CaseClassDef(_, _, None, _) => c
    }

  }

  // A class that represents flags that annotate a FunDef with different attributes
  sealed trait FunctionFlag

  object FunctionFlag {
    def fromName(name: String, args: Seq[Option[Any]]): FunctionFlag = name match {
      case "inline" => IsInlined
      case _ => Annotation(name, args)
    }
  }

  // A class that represents flags that annotate a ClassDef with different attributes
  sealed trait ClassFlag

  object ClassFlag {
    def fromName(name: String, args: Seq[Option[Any]]): ClassFlag = Annotation(name, args)
  }

  // Whether this FunDef was originally a (lazy) field
  case class IsField(isLazy: Boolean) extends FunctionFlag
  // Compiler annotations given in the source code as @annot
  case class Annotation(annot: String, args: Seq[Option[Any]]) extends FunctionFlag with ClassFlag
  // If this class was a method. owner is the original owner of the method
  case class IsMethod(owner: ClassDef) extends FunctionFlag
  // If this function represents a loop that was there before XLangElimination
  // Contains a copy of the original looping function
  case class IsLoop(orig: FunDef) extends FunctionFlag
  // If extraction fails of the function's body fais, it is marked as abstract
  case object IsAbstract extends FunctionFlag
  // Currently, the only synthetic functions are those that calculate default values of parameters
  case object IsSynthetic extends FunctionFlag
  // Is inlined
  case object IsInlined extends FunctionFlag


  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassDef extends Definition {
    self =>

    def subDefinitions = fields ++ methods ++ tparams 
      
    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    def fields: Seq[ValDef]
    val parent: Option[AbstractClassType]

    def hasParent = parent.isDefined

    def fieldsIds = fields.map(_.id)

    private var _children: List[ClassDef] = Nil

    def registerChild(chd: ClassDef) = {
      _children = (chd :: _children).sortBy(_.id.name)
    }

    private var _methods = List[FunDef]()

    def registerMethod(fd: FunDef) = {
      _methods = _methods ::: List(fd)
    }

    def unregisterMethod(id: Identifier) = {
      _methods = _methods filterNot (_.id == id)
    }

    def clearMethods() {
      _methods = Nil
    }

    def methods = _methods

    private var _flags: Set[ClassFlag] = Set()

    def addFlags(flags: Set[ClassFlag]): this.type = {
      this._flags ++= flags
      this
    }

    def addFlag(flag: ClassFlag): this.type = addFlags(Set(flag))

    def flags = _flags

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect { case Annotation(s, args) => s -> args }.toMap

    lazy val ancestors: Seq[ClassDef] = parent.toSeq flatMap { p => p.classDef +: p.classDef.ancestors }

    lazy val root = ancestors.lastOption.getOrElse(this)

    def knownChildren: Seq[ClassDef] = _children

    def knownDescendants: Seq[ClassDef] = {
      knownChildren ++ knownChildren.flatMap {
        case acd: AbstractClassDef => acd.knownDescendants
        case _ => Nil
      }
    }

    def knownCCDescendants: Seq[CaseClassDef] = knownDescendants.collect {
      case ccd: CaseClassDef =>
        ccd
    }

    val isAbstract: Boolean
    val isCaseObject: Boolean

    lazy val definedFunctions : Seq[FunDef] = methods
    lazy val definedClasses = Seq(this)

    def typed(tps: Seq[TypeTree]): ClassType
    def typed: ClassType
  }

  /** Abstract classes. */
  case class AbstractClassDef(id: Identifier,
                              tparams: Seq[TypeParameterDef],
                              parent: Option[AbstractClassType]) extends ClassDef {

    val fields = Nil
    val isAbstract   = true
    val isCaseObject = false
    
    lazy val singleCaseClasses : Seq[CaseClassDef] = Nil

    def typed(tps: Seq[TypeTree]) = {
      require(tps.length == tparams.length)
      AbstractClassType(this, tps)
    }
    def typed: AbstractClassType = typed(tparams.map(_.tp))
  }

  /** Case classes/objects. */
  case class CaseClassDef(id: Identifier,
                          tparams: Seq[TypeParameterDef],
                          parent: Option[AbstractClassType],
                          isCaseObject: Boolean) extends ClassDef {

    private var _fields = Seq[ValDef]()

    def fields = _fields

    def setFields(fields: Seq[ValDef]) {
      _fields = fields
    }

    val isAbstract = false

    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.indexWhere(_.id == id)

      if (index < 0) {
        scala.sys.error(
          "Could not find '"+id+"' ("+id.uniqueName+") within "+
          fields.map(_.id.uniqueName).mkString(", ")
        )
      } else index
    }
    
    lazy val singleCaseClasses : Seq[CaseClassDef] = if (hasParent) Nil else Seq(this)

    def typed(tps: Seq[TypeTree]): CaseClassType = {
      require(tps.length == tparams.length)
      CaseClassType(this, tps)
    }
    def typed: CaseClassType = typed(tparams.map(_.tp))
  }

  /** Function/method definition.
    *
    *  This class represents methods or fields of objects or classes. By "fields" we mean
    *  fields defined in the body of a class/object, not the constructor arguments of a case class
    *  (those are accessible through [[leon.purescala.Definitions.ClassDef.fields]]).
    *
    *  When it comes to verification, all are treated the same (as functions).
    *  They are only differentiated when it comes to code generation/ pretty printing.
    *  By default, the FunDef represents a function/method as opposed to a field,
    *  unless otherwise specified by its flags.
    *
    *  Bear in mind that [[id]] will not be consistently typed.
    */
  class FunDef(
    val id: Identifier,
    val tparams: Seq[TypeParameterDef],
    val returnType: TypeTree,
    val params: Seq[ValDef]
  ) extends Definition {

    /* Body manipulation */
    
    private var fullBody_ : Expr = NoTree(returnType)
    def fullBody = fullBody_
    def fullBody_= (e : Expr) {
      fullBody_ = e
    }

    def body: Option[Expr] = withoutSpec(fullBody)
    def body_=(b: Option[Expr]) = {
      fullBody = withBody(fullBody, b)
    }

    def precondition = preconditionOf(fullBody)
    def precondition_=(oe: Option[Expr]) = {
      fullBody = withPrecondition(fullBody, oe) 
    }

    def postcondition = postconditionOf(fullBody)
    def postcondition_=(op: Option[Expr]) = {
      fullBody = withPostcondition(fullBody, op) 
    }

    def hasBody                     = body.isDefined
    def hasPrecondition : Boolean   = precondition.isDefined
    def hasPostcondition : Boolean  = postcondition.isDefined

    def isRecursive(p: Program) = p.callGraph.transitiveCallees(this) contains this
    
    /* Nested definitions */
    def nestedFuns = directlyNestedFunDefs(fullBody)
    def subDefinitions = params ++ tparams ++ nestedFuns.toList

    /* Duplication */
    
    def duplicate: FunDef = {
      val fd = new FunDef(id.freshen, tparams, returnType, params)
      fd.copyContentFrom(this)
      fd.copiedFrom(this)
    }
    
    def copyContentFrom(from : FunDef) {
      this.fullBody  = from.fullBody 
      this.addFlags(from.flags)
    }

    /* Flags */

    private[this] var _flags: Set[FunctionFlag] = Set()

    def addFlags(flags: Set[FunctionFlag]): FunDef = {
      this._flags ++= flags
      this
    }

    def addFlag(flag: FunctionFlag): FunDef = addFlags(Set(flag))

    def flags = _flags

    def annotations: Set[String] = extAnnotations.keySet
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect { case Annotation(s, args) => s -> args }.toMap
    def canBeLazyField    = flags.contains(IsField(true))  && params.isEmpty && tparams.isEmpty
    def canBeStrictField  = flags.contains(IsField(false)) && params.isEmpty && tparams.isEmpty
    def canBeField        = canBeLazyField || canBeStrictField
    def isRealFunction    = !canBeField
    def isSynthetic       = flags contains IsSynthetic
    def methodOwner       = flags collectFirst { case IsMethod(cd) => cd }

    /* Wrapping in TypedFunDef */
    
    def typed(tps: Seq[TypeTree]) = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed = {
      TypedFunDef(this, tparams.map(_.tp))
    }

    def qualifiedName(implicit pgm: Program) = DefOps.qualifiedName(this, false)

  }


  // Wrapper for typing function according to valuations for type parameters
  case class TypedFunDef(fd: FunDef, tps: Seq[TypeTree]) extends Tree {
    val id = fd.id

    def signature = {
      if (tps.nonEmpty) {
        id.toString+tps.mkString("[", ", ", "]")
      } else {
        id.toString
      }
    }

    private lazy val typesMap: Map[TypeParameterDef, TypeTree] = {
      (fd.tparams zip tps).toMap.filter(tt => tt._1.tp != tt._2)
    }

    def translated(t: TypeTree): TypeTree = instantiateType(t, typesMap)

    def translated(e: Expr): Expr = instantiateType(e, typesMap, paramsMap)

    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == params.size)
      (params map { _.id } zip realArgs).toMap
    }

    def withParamSubst(realArgs: Seq[Expr], e: Expr) = {
      replaceFromIDs(paramSubst(realArgs), e)
    }

    def applied(realArgs: Seq[Expr]): FunctionInvocation = {
      FunctionInvocation(this, realArgs)
    }

    def applied: FunctionInvocation =
      applied(params map { _.toVariable })

    /** 
     *  Params will return ValDefs instantiated with the correct types
     *  For such a ValDef(id,tp) it may hold that (id.getType != tp)  
     */
    lazy val (params: Seq[ValDef], paramsMap: Map[Identifier, Identifier]) = {
      if (typesMap.isEmpty) {
        (fd.params, Map())
      } else {
        val newParams = fd.params.map {
          case vd @ ValDef(id, _) =>
            val newTpe = translated(vd.getType)
            val newId = FreshIdentifier(id.name, newTpe, true).copiedFrom(id)
            ValDef(newId).setPos(vd)
        }

        val paramsMap: Map[Identifier, Identifier] = (fd.params zip newParams).map { case (vd1, vd2) => vd1.id -> vd2.id }.toMap

        (newParams, paramsMap)
      }
    }

    lazy val functionType = FunctionType(params.map(_.getType).toList, returnType)

    lazy val returnType: TypeTree = translated(fd.returnType)

    private var trCache = Map[Expr, Expr]()

    private def cached(e: Expr): Expr = {
      trCache.getOrElse(e, {
        val res = translated(e)
        trCache += e -> res
        res
      })
    }

    def fullBody      = cached(fd.fullBody)
    def body          = fd.body map cached
    def precondition  = fd.precondition map cached
    def postcondition = fd.postcondition map cached

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined

    override def getPos = fd.getPos
  }
}
