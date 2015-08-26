/* Copyright 2009-2015 EPFL, Lausanne */

package leon.reflect.purescala

import leon._
import lang._
import collection._
import string._

import Common._
import Expressions._
//import ExprOps._
import Types._
//import TypeOps._

object Definitions {

  /** 
   *  A ValDef declares a new identifier to be of a certain type.
   *  The optional tpe, if present, overrides the type of the underlying Identifier id
   *  This is useful to instantiate argument types of polymorphic functions
   */
  case class ValDef(id: Identifier, tpe: Option[TypeTree]) {

    val getType = tpe getOrElse id.getType

    // Warning: the variable will not have the same type as the ValDef, but 
    // the Identifier type is enough for all use cases in Leon
    def toVariable : Variable = Variable(id)
  }

  /** A wrapper for a program. For now a program is simply a single object. */
  case class Program(units: List[UnitDef]) {
    val id = FreshIdentifier("program")

    def definedFunctions    = units.flatMap(_.definedFunctions)
    def definedClasses      = units.flatMap(_.definedClasses)
    def classHierarchyRoots = units.flatMap(_.classHierarchyRoots)
    def singleCaseClasses   = units.flatMap(_.singleCaseClasses)
    def modules             = units.flatMap(_.defs)

  }

  case class TypeParameterDef(id: Identifier) { // FIXME TypeParameter
    def freshen = TypeParameterDef(id.freshen)
    def tp = TypeParameter(id)
  }
 
  case class UnitDef(
    id: Identifier,
    defs : List[ModuleDef],
    isMainUnit : Boolean // false for libraries/imports
  ) {
     
    def definedFunctions: List[FunDef] = defs.flatMap { _.definedFunctions }

    def definedClasses = defs.flatMap { _.definedClasses }

    def classHierarchyRoots = {
      definedClasses.filter(!_.hasParent)
    }

    // Guarantees that a parent always appears before its children
    def classHierarchies = classHierarchyRoots map { root =>
      root :: root.knownDescendants
    }

    def singleCaseClasses = {
      definedClasses.flatMap {
        case ccd: CaseClassDef if !ccd.hasParent => List(ccd)
        case _ => Nil[CaseClassDef]()
      }
    }

    def modules = defs.flatMap {
      case md: ModuleDef => List(md)
      case _ => Nil[ModuleDef]()
    }
  }
  
  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(
    id: Identifier,
    definedClasses: List[ClassDef],
    definedFunctions: List[FunDef],
    isPackageObject: Boolean
  ) {
    
    lazy val classHierarchyRoots : List[ClassDef] = definedClasses.filter{ !_.hasParent }

    lazy val singleCaseClasses : List[CaseClassDef] = definedClasses.flatMap {
      case c @ CaseClassDef(_, _, _, _, _, None()) => List(c)
      case _ => Nil[CaseClassDef]()
    }

  }

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed abstract class ClassDef {
    val id: Identifier
    val tparams: List[TypeParameterDef]
    val fields: List[ValDef]
    val parent: Option[ClassType]
    val children: List[ClassDef]
    val methods: List[FunDef]

    def hasParent = parent.isDefined

    def fieldsIds = fields.map(_.id)

    lazy val ancestors: List[ClassDef] = parent.toList flatMap { p => p.classDef :: p.classDef.ancestors }

    lazy val root = ancestors.lastOption.getOrElse(this)

    def knownChildren: List[ClassDef] = children

    def knownDescendants: List[ClassDef] = {
      knownChildren ++ knownChildren.flatMap {
        case acd: AbstractClassDef => acd.knownDescendants
        case _ => Nil()
      }
    }

    def knownCCDescendants: List[CaseClassDef] = knownDescendants.flatMap {
      case ccd: CaseClassDef => List(ccd)
      case _ => Nil[CaseClassDef]()
    }

    val isAbstract: Boolean
    val isCaseObject: Boolean

    lazy val definedFunctions: List[FunDef] = methods
    lazy val definedClasses = List(this)

    def typed(tps: List[TypeTree]): ClassType
    def typed: ClassType
  }

  /** Abstract classes. */
  case class AbstractClassDef(
    id: Identifier,
    tparams: List[TypeParameterDef],
    parent: Option[ClassType],
    methods: List[FunDef],
    children: List[ClassDef]
  ) extends ClassDef {

    val fields = Nil[ValDef]()
    val isAbstract   = true
    val isCaseObject = false
    
    lazy val singleCaseClasses: List[CaseClassDef] = Nil[CaseClassDef]()

    def typed(tps: List[TypeTree]) = {
      require(tps.length == tparams.length)
      AbstractClassType(this, tps)
    }
    def typed: AbstractClassType = typed(tparams.map(_.tp))
  }

  /** Case classes/objects. */
  case class CaseClassDef(
    id: Identifier,
    tparams: List[TypeParameterDef],
    fields: List[ValDef],
    isCaseObject: Boolean,
    methods: List[FunDef],
    parent: Option[ClassType]
  ) extends ClassDef {

    val children = Nil[ClassDef]()
    val isAbstract = false

    def selectorID2Index(id: Identifier): BigInt = {
      fields.indexWhere(_.id == id)
    }
    
    lazy val singleCaseClasses : List[CaseClassDef] = if (hasParent) Nil() else List(this)

    def typed(tps: List[TypeTree]): CaseClassType = {
      require(tps.length == tparams.length)
      CaseClassType(this, tps)
    }
    def typed: CaseClassType = typed(tparams.map(_.tp))
  }

  // Whether this FunDef was originally a (lazy) field
  case class IsField(isLazy: Boolean)

  /** Functions
    *  This class represents methods or fields of objects. By "fields" we mean
    *  fields defined in the body, not the constructor arguments of a case class.
    *  When it comes to verification, all are treated the same (as functions).
    *  They are only differentiated when it comes to code generation/ pretty printing.
    *  By default, the FunDef represents a function/method, unless otherwise specified
    *  by its flags.
    */
  case class FunDef(
    id: Identifier,
    tparams: List[TypeParameterDef],
    returnType: TypeTree,
    fullBody: Expr,
    params: List[ValDef],
    isField: IsField
  ) {

    /* Body manipulation */
    
    def body: Option[Expr] = None[Expr]() // FIXME withoutSpec(fullBody)

    def precondition = None[Expr]()// FIXME preconditionOf(fullBody)

    def postcondition = None[Expr]() // FIXME postconditionOf(fullBody)

    def hasBody                     = body.isDefined
    def hasPrecondition : Boolean   = precondition.isDefined
    def hasPostcondition : Boolean  = postcondition.isDefined

    /* Wrapping in TypedFunDef */
    
    def typed(tps: List[TypeTree]) = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed = {
      TypedFunDef(this, tparams.map(_.tp))
    }

  }


  // Wrapper for typing function according to valuations for type parameters
  case class TypedFunDef(fd: FunDef, tps: List[TypeTree]) {
    val id = fd.id

    private lazy val typesMap: Map[TypeParameterDef, TypeTree] = {
      ListOps.toMap((fd.tparams zip tps).filter(tt => tt._1.tp != tt._2))
    }

    def translated(t: TypeTree): TypeTree = t // FIXME instantiateType(t, typesMap)

    def translated(e: Expr): Expr = e // FIXME instantiateType(e, typesMap, paramsMap)

    def paramSubst(realArgs: List[Expr]) = {
      require(realArgs.size == params.size)
      ListOps.toMap(params map { _.id } zip realArgs)
    }

    def withParamSubst(realArgs: List[Expr], e: Expr) = {
      e // FIXME replaceFromIDs(paramSubst(realArgs), e)
    }

    def applied(realArgs: List[Expr]): FunctionInvocation = {
      FunctionInvocation(this, realArgs)
    }

    def applied: FunctionInvocation =
      applied(params map { _.toVariable })

    /** 
     *  Params will return ValDefs instantiated with the correct types
     *  For such a ValDef(id,tp) it may hold that (id.getType != tp)  
     */
    lazy val paramsAndMap: (List[ValDef], Map[Identifier, Identifier]) = {
      if (typesMap == Map[TypeParameterDef, TypeTree]()) {
        (fd.params, Map[Identifier, Identifier]())
      } else {
        val newParams = fd.params.map {
          case vd @ ValDef(id, _) =>
            val newTpe = translated(vd.getType)
            val newId = FreshIdentifier(id.name, newTpe, true)
            ValDef(newId, None())
        }

        val paramsMap: Map[Identifier, Identifier] = (fd.params zip newParams).foldLeft(Map[Identifier, Identifier]()) { 
          case (current, (vd1, vd2)) => 
            current ++ Map(vd1.id -> vd2.id)
        }

        (newParams, paramsMap)
      }
    }
    
    lazy val params: List[ValDef] = paramsAndMap._1
    lazy val paramsMap: Map[Identifier, Identifier] = paramsAndMap._2

    lazy val functionType = FunctionType(params.map(_.getType), returnType)

    lazy val returnType: TypeTree = translated(fd.returnType)

    private def cached(e: Expr): Expr = {
      translated(e)
    }

    def fullBody      = cached(fd.fullBody)
    def body          = fd.body map cached
    def precondition  = fd.precondition map cached
    def postcondition = fd.postcondition map cached

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined

  }
}
