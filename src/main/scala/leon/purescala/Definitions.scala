/* Copyright 2009-2016 EPFL, Lausanne */

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

    def subDefinitions: Seq[Definition] // The enclosed scopes/definitions by this definition
  
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

  /** 
   *  A ValDef declares a new identifier to be of a certain type.
   *  The optional tpe, if present, overrides the type of the underlying Identifier id
   *  This is useful to instantiate argument types of polymorphic functions
   */
  case class ValDef(id: Identifier) extends Definition with Typed {
    self: Serializable =>

    val getType = id.getType

    var defaultValue : Option[FunDef] = None

    var isVar: Boolean = false

    def setIsVar(b: Boolean): this.type = { this.isVar = b; this }

    def subDefinitions = Seq()

    /** Transform this [[ValDef]] into a [[Expressions.Variable Variable]] */
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
    
    def lookupCaseClass(name: String) = lookupAll(name).collect{ case c: CaseClassDef => c }.headOption
    def lookupAbstractClass(name: String) = lookupAll(name).collect{ case c: AbstractClassDef => c }.headOption
    def lookupFunDef(name: String) = lookupAll(name).collect{ case c: FunDef => c }.headOption
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

  /** Definition of a compilation unit, corresponding to a source file
    *
    * @param id The name of the file this [[UnitDef]] was compiled from
    * @param pack The package of this [[UnitDef]]
    * @param imports The imports of this [[UnitDef]]
    * @param defs The [[Definition]]s (classes and objects) in this [[UnitDef]]
    * @param isMainUnit Whether this is a user-provided file or a library file
    */
  case class UnitDef(
    id: Identifier,
    pack: PackageRef,
    imports: Seq[Import],
    defs: Seq[Definition],
    isMainUnit: Boolean
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
      UnitDef(id, Nil, Nil, modules, true)
  }
  
  /** Corresponds to an '''object''' in scala. Contains [[FunDef]]s, [[ClassDef]]s and [[ValDef]]s. */
  case class ModuleDef(id: Identifier, defs: Seq[Definition], isPackageObject: Boolean) extends Definition {
    
    def subDefinitions = defs
    
    lazy val definedFunctions : Seq[FunDef] = defs.collect { case fd: FunDef => fd }

    lazy val definedClasses : Seq[ClassDef] = defs.collect { case ctd: ClassDef => ctd }

    lazy val classHierarchyRoots : Seq[ClassDef] = defs.collect {
      case ctd: ClassDef if !ctd.hasParent => ctd
    }

    lazy val algebraicDataTypes : Map[AbstractClassDef, Seq[CaseClassDef]] = defs.collect {
      case c : CaseClassDef if c.parent.isDefined => c
    }.groupBy(_.parent.get.classDef)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c : CaseClassDef if !c.parent.isDefined => c
    }
  }

  /** A trait that represents flags that annotate a ClassDef with different attributes */
  sealed trait ClassFlag

  object ClassFlag {
    def fromName(name: String, args: Seq[Option[Any]]): ClassFlag = Annotation(name, args)
  }

  /** A trait that represents flags that annotate a FunDef with different attributes */
  sealed trait FunctionFlag

  object FunctionFlag {
    def fromName(name: String, args: Seq[Option[Any]]): FunctionFlag = name match {
      case "inline" => IsInlined
      case _ => Annotation(name, args)
    }
  }

  // Whether this FunDef was originally a (lazy) field
  case class IsField(isLazy: Boolean) extends FunctionFlag
  // Compiler annotations given in the source code as @annot
  case class Annotation(annot: String, args: Seq[Option[Any]]) extends FunctionFlag with ClassFlag
  // If this class was a method. owner is the original owner of the method
  case class IsMethod(owner: ClassDef) extends FunctionFlag
  // If this function represents a loop that was there before XLangElimination
  // Contains a link to the FunDef where the loop was defined
  case class IsLoop(owner: FunDef) extends FunctionFlag
  // If extraction fails of the function's body fais, it is marked as abstract
  case object IsAbstract extends FunctionFlag
  // Currently, the only synthetic functions are those that calculate default values of parameters
  case object IsSynthetic extends FunctionFlag
  // Is inlined
  case object IsInlined extends FunctionFlag
  // Is an ADT invariant method
  case object IsADTInvariant extends FunctionFlag
  case object IsInner extends FunctionFlag

  /** Represents a class definition (either an abstract- or a case-class) */
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

    private var _invariant: Option[FunDef] = None

    def invariant: Option[FunDef] = parent.flatMap(_.classDef.invariant).orElse(_invariant)
    def setInvariant(fd: FunDef): Unit = parent match {
      case Some(act) => act.classDef.setInvariant(fd)
      case None => _invariant = Some(fd)
    }

    def hasInvariant: Boolean = invariant.isDefined || (this +: root.knownDescendants).exists(cd => cd.methods.exists(_.isInvariant))

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

    def isInductive: Boolean = {
      def induct(tpe: TypeTree, seen: Set[ClassDef]): Boolean = tpe match {
        case ct: ClassType =>
          val root = ct.classDef.root
          seen(root) || ct.fields.forall(vd => induct(vd.getType, seen + root))
        case TupleType(tpes) =>
          tpes.forall(tpe => induct(tpe, seen))
        case _ => true
      }

      if (this == root && !this.isAbstract) false
      else if (this != root) root.isInductive
      else knownCCDescendants.forall { ccd =>
        ccd.fields.forall(vd => induct(vd.getType, Set(root)))
      }
    }

    val isAbstract: Boolean
    val isCaseObject: Boolean

    lazy val definedFunctions : Seq[FunDef] = methods
    lazy val definedClasses = Seq(this)

    def typeArgs = tparams map (_.tp)

    def typed(tps: Seq[TypeTree]): ClassType
    def typed: ClassType
  }

  /** Abstract classes. */
  class AbstractClassDef(val id: Identifier,
                         val tparams: Seq[TypeParameterDef],
                         val parent: Option[AbstractClassType]) extends ClassDef {

    val fields = Nil
    val isAbstract   = true
    val isCaseObject = false
    
    lazy val singleCaseClasses : Seq[CaseClassDef] = Nil

    def typed(tps: Seq[TypeTree]) = {
      require(tps.length == tparams.length)
      AbstractClassType(this, tps)
    }
    def typed: AbstractClassType = typed(tparams.map(_.tp))
    
    /** Duplication of this [[CaseClassDef]].
      * @note This will not add known case class children
      */
    def duplicate(
      id: Identifier                    = this.id.freshen,
      tparams: Seq[TypeParameterDef]    = this.tparams,
      parent: Option[AbstractClassType] = this.parent
    ): AbstractClassDef = {
      val acd = new AbstractClassDef(id, tparams, parent)
      acd.addFlags(this.flags)
      if (!parent.exists(_.classDef.hasInvariant)) invariant.foreach(inv => acd.setInvariant(inv))
      parent.foreach(_.classDef.registerChild(acd))
      acd.copiedFrom(this)
    }
  }

  /** Case classes/ case objects. */
  class CaseClassDef(val id: Identifier,
                     val tparams: Seq[TypeParameterDef],
                     val parent: Option[AbstractClassType],
                     val isCaseObject: Boolean) extends ClassDef {

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

    def typed: CaseClassType = typed(tparams.map(_.tp))
    def typed(tps: Seq[TypeTree]): CaseClassType = {
      require(tps.length == tparams.length)
      CaseClassType(this, tps)
    }
    
    /** Duplication of this [[CaseClassDef]].
      * @note This will not replace recursive [[CaseClassDef]] calls in [[fields]] nor the parent abstract class types
      */
    def duplicate(
      id: Identifier                    = this.id.freshen,
      tparams: Seq[TypeParameterDef]    = this.tparams,
      fields: Seq[ValDef]               = this.fields,
      parent: Option[AbstractClassType] = this.parent,
      isCaseObject: Boolean             = this.isCaseObject
    ): CaseClassDef = {
      val cd = new CaseClassDef(id, tparams, parent, isCaseObject)
      cd.setFields(fields)
      cd.addFlags(this.flags)
      if (!parent.exists(_.classDef.hasInvariant)) invariant.foreach(inv => cd.setInvariant(inv))
      parent.foreach(_.classDef.registerChild(cd))
      cd.copiedFrom(this)
    }
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
    val params: Seq[ValDef],
    val returnType: TypeTree
  ) extends Definition {

    /* Body manipulation */
    
    var fullBody: Expr = NoTree(returnType)
    
    def body: Option[Expr] = withoutSpec(fullBody)
    def body_=(b: Option[Expr]) = {
      fullBody = withBody(fullBody, b)
    }

    def precondition = preconditionOf(fullBody)
    def precondition_=(oe: Option[Expr]) = {
      fullBody = withPrecondition(fullBody, oe)
    }
    def precondition_=(p: Path) = {
      fullBody = withPath(fullBody, p)
    }
    def precOrTrue = precondition getOrElse BooleanLiteral(true)

    def postcondition = postconditionOf(fullBody)
    def postcondition_=(op: Option[Expr]) = {
      fullBody = withPostcondition(fullBody, op) 
    }
    def postOrTrue = postcondition getOrElse {
      val arg = ValDef(FreshIdentifier("res", returnType, alwaysShowUniqueID = true))
      Lambda(Seq(arg), BooleanLiteral(true))
    }

    def hasBody          = body.isDefined
    def hasPrecondition  = precondition.isDefined
    def hasPostcondition = postcondition.isDefined
    
    /* Nested definitions */
    def directlyNestedFuns = directlyNestedFunDefs(fullBody)
    def subDefinitions = params ++ tparams ++ directlyNestedFuns.toList

    /** Duplication of this [[FunDef]].
      * @note This will not replace recursive function calls in [[fullBody]]
      */
    def duplicate(
      id: Identifier                  = this.id.freshen,
      tparams: Seq[TypeParameterDef]  = this.tparams,
      params: Seq[ValDef]             = this.params,
      returnType: TypeTree            = this.returnType
    ): FunDef = {
      val fd = new FunDef(id, tparams, params, returnType)
      fd.fullBody = this.fullBody
      fd.addFlags(this.flags)
      fd.copiedFrom(this)
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
    def extAnnotations: Map[String, Seq[Option[Any]]] = flags.collect {
      case Annotation(s, args) => s -> args
    }.toMap
    def canBeLazyField    = flags.contains(IsField(true))  && params.isEmpty && tparams.isEmpty
    def canBeStrictField  = flags.contains(IsField(false)) && params.isEmpty && tparams.isEmpty
    def canBeField        = canBeLazyField || canBeStrictField
    def isRealFunction    = !canBeField
    def isSynthetic       = flags contains IsSynthetic
    def isInvariant       = flags contains IsADTInvariant
    def isInner           = flags contains IsInner
    def methodOwner       = flags collectFirst { case IsMethod(cd) => cd }

    /* Wrapping in TypedFunDef */
    
    def typed(tps: Seq[TypeTree]): TypedFunDef = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed: TypedFunDef = typed(tparams.map(_.tp))

    /* Auxiliary methods */

    def qualifiedName(implicit pgm: Program) = DefOps.qualifiedName(this, useUniqueIds = false)

    def isRecursive(p: Program) = p.callGraph.transitiveCallees(this) contains this

    def paramIds = params map { _.id }

    def typeArgs = tparams map (_.tp)

    def applied(args: Seq[Expr]): FunctionInvocation = Constructors.functionInvocation(this, args)
    def applied = FunctionInvocation(this.typed, this.paramIds map Variable)
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

    private lazy val typesMap: Map[TypeParameter, TypeTree] = {
      (fd.typeArgs zip tps).toMap.filter(tt => tt._1 != tt._2)
    }

    def translated(t: TypeTree): TypeTree = instantiateType(t, typesMap)

    def translated(e: Expr): Expr = instantiateType(e, typesMap, paramsMap)

    /** A mapping from this [[TypedFunDef]]'s formal parameters to real arguments
      *
      * @param realArgs The arguments to which the formal argumentas are mapped
      * */
    def paramSubst(realArgs: Seq[Expr]) = {
      require(realArgs.size == params.size)
      (paramIds zip realArgs).toMap
    }

    /** Substitute this [[TypedFunDef]]'s formal parameters with real arguments in some expression
     *
     * @param realArgs The arguments to which the formal argumentas are mapped
     * @param e The expression in which the substitution will take place
     */
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
        val newParams = fd.params.map { vd =>
          val newTpe = translated(vd.getType)
          val newId = FreshIdentifier(vd.id.name, newTpe, true).copiedFrom(vd.id)
          vd.copy(id = newId).setPos(vd)
        }

        val paramsMap: Map[Identifier, Identifier] = (fd.params zip newParams).map { case (vd1, vd2) => vd1.id -> vd2.id }.toMap

        (newParams, paramsMap)
      }
    }

    lazy val functionType = FunctionType(params.map(_.getType).toList, returnType)

    lazy val returnType: TypeTree = translated(fd.returnType)

    lazy val paramIds = params map { _.id }

    private var trCache = Map[Expr, Expr]()

    private def cached(e: Expr): Expr = {
      trCache.getOrElse(e, {
        val res = translated(e)
        trCache += e -> res
        res
      })
    }

    // Methods that extract expressions from the underlying FunDef, using a cache

    def fullBody      = cached(fd.fullBody)
    def body          = fd.body map cached
    def precondition  = fd.precondition map cached
    def precOrTrue    = cached(fd.precOrTrue)
    def postcondition = fd.postcondition map cached
    def postOrTrue    = cached(fd.postOrTrue)

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined

    override def getPos = fd.getPos
  }
}
