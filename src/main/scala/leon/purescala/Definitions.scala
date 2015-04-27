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
    
    def owner = id.owner
    def setOwner(owner : Definition) : this.type = { id.owner = Some(owner); this }
    
    var origOwner : Option[Definition] = None // The definition/scope enclosing this definition
    
    def subDefinitions : Seq[Definition]      // The enclosed scopes/definitions by this definition
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }
    override def copiedFrom(o : Tree) : this.type = {
      super.copiedFrom(o)
      o match {
        case df : Definition if df.owner.isDefined =>
          this.setOwner(df.owner.get)
        case _ =>
          this
      }
      
    }

    def setSubDefOwners() = for (df <- subDefinitions) df.setOwner(this)
     
  }

  /** 
   *  A ValDef declares a new identifier to be of a certain type.
   *  The optional tpe, if present, overrides the type of the underlying Identifier id
   *  This is useful to instantiate argument types of polymorphic functions
   */
  case class ValDef(id: Identifier, tpe: Option[TypeTree] = None) extends Definition with Typed {
    self: Serializable =>

    val getType = tpe getOrElse id.getType

    var defaultValue : Option[FunDef] = None
      
    def subDefinitions = Seq()

    // Warning: the variable will not have the same type as the ValDef, but 
    // the Identifier type is enough for all use cases in Leon
    def toVariable : Variable = Variable(id)

    setSubDefOwners()
  }

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, units: List[UnitDef]) extends Definition {
    origOwner = None
    def subDefinitions = units
    
    def definedFunctions    = units.flatMap(_.definedFunctions)
    def definedClasses      = units.flatMap(_.definedClasses)
    def classHierarchyRoots = units.flatMap(_.classHierarchyRoots)
    def algebraicDataTypes  = units.flatMap(_.algebraicDataTypes).toMap
    def singleCaseClasses   = units.flatMap(_.singleCaseClasses)
    def modules             = units.flatMap(_.modules)
    
    lazy val callGraph      = new CallGraph(this)

    def caseClassDef(name: String) = definedClasses.collect {
      case ccd: CaseClassDef if ccd.id.name == name => ccd
    }.headOption.getOrElse(throw LeonFatalError("Unknown case class '"+name+"'"))

    def duplicate = {
      copy(units = units.map{_.duplicate})
    }

    lazy val library = Library(this)
    
    def writeScalaFile(filename: String) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this))
      out.close()
    }
    setSubDefOwners()
  }

  object Program {
    lazy val empty : Program = Program(
      FreshIdentifier("empty"),
      Nil
    )
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def subDefinitions = Seq()
    def freshen = TypeParameterDef(tp.freshen)
    val id = tp.id
    setSubDefOwners()
  }
 
  /** A package as a path of names */
  type PackageRef = List[String] 

  abstract class Import extends Definition {
    def subDefinitions = Nil
    
    def importedDefs = this match {
      case PackageImport(pack) => {
        import DefOps._
        // Ignore standalone modules, assume there are extra imports for them
        programOf(this) map { unitsInPackage(_,pack) } getOrElse List()
      }
      case SingleImport(imported) => List(imported)
      case WildcardImport(imported) => imported.subDefinitions
    }
  }
   
  // import pack._
  case class PackageImport(pack : PackageRef) extends Import {
    val id = FreshIdentifier("import " + (pack mkString "."))
  }
  // import pack.(...).df
  case class SingleImport(df : Definition) extends Import {
    val id = FreshIdentifier(s"import ${df.id.toString}")
  }
  // import pack.(...).df._
  case class WildcardImport(df : Definition) extends Import {
    val id = FreshIdentifier(s"import ${df.id.toString}._")
  }
  
    
  case class UnitDef(
    id: Identifier,
    modules : Seq[ModuleDef],
    pack : PackageRef,
    imports : Seq[Import],
    isMainUnit : Boolean // false for libraries/imports
  ) extends Definition {
     
    def subDefinitions = modules ++ imports
    
    def definedFunctions    = modules.flatMap(_.definedFunctions)
    def definedClasses      = modules.flatMap(_.definedClasses)
    def classHierarchyRoots = modules.flatMap(_.classHierarchyRoots)
    def algebraicDataTypes  = modules.flatMap(_.algebraicDataTypes)
    def singleCaseClasses   = modules.flatMap(_.singleCaseClasses)

    def duplicate = {
      copy(modules = modules map { _.duplicate } )
    }
    
    def writeScalaFile(filename: String) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this))
      out.close()
    }
    
    setSubDefOwners()
  }
  
  object UnitDef {
    def apply(id: Identifier, modules : Seq[ModuleDef]) : UnitDef = 
      UnitDef(id,modules, Nil,Nil,true)
  }
  
  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(id: Identifier, defs : Seq[Definition], isStandalone : Boolean) extends Definition {
    
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
    
    def duplicate = copy(defs = defs map {
      case f: FunDef => f.duplicate
      case cd: ClassDef => cd.duplicate
      case other => other
    })
      
    setSubDefOwners()

  }

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

    def registerChildren(chd: ClassDef) = {
      _children = (chd :: _children).sortBy(_.id.name)
    }

    private var _methods = List[FunDef]()

    def registerMethod(fd: FunDef) = {
      _methods = _methods ::: List(fd)
      fd.setOwner(this)
    }

    def clearMethods() {
      _methods = Nil
    }

    def methods = _methods

    def knownChildren: Seq[ClassDef] = _children

    def knownDescendents: Seq[ClassDef] = {
      knownChildren ++ (knownChildren.map {
        case acd: AbstractClassDef => acd.knownDescendents
        case _ => Nil
      }.foldLeft(List[ClassDef]())(_ ++ _))
    }

    def knownCCDescendents: Seq[CaseClassDef] = knownDescendents.collect {
      case ccd: CaseClassDef =>
        ccd
    }

    val isAbstract: Boolean
    val isCaseObject: Boolean
    
    def duplicate = this match {
      case ab : AbstractClassDef => {
        val ab2 = ab.copy()
        ab.knownChildren foreach ab2.registerChildren
        ab.methods foreach { m => ab2.registerMethod(m.duplicate) }
        ab2
      }
      case cc : CaseClassDef => {
        val cc2 = cc.copy() 
        cc.methods foreach { m => cc2.registerMethod(m.duplicate) }
        cc2.setFields(cc.fields map { _.copy() })
        cc2
      }
    }
    
    lazy val definedFunctions : Seq[FunDef] = methods
    lazy val definedClasses = Seq(this)
    lazy val classHierarchyRoots = if (this.hasParent) Seq(this) else Nil
    
  }

  /** Abstract classes. */
  case class AbstractClassDef(id: Identifier,
                              tparams: Seq[TypeParameterDef],
                              parent: Option[AbstractClassType]) extends ClassDef {

    val fields = Nil
    val isAbstract   = true
    val isCaseObject = false
    
    lazy val singleCaseClasses : Seq[CaseClassDef] = Nil
    setSubDefOwners()
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
      _fields foreach { _.setOwner(this)}
    }


    val isAbstract = false


    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.zipWithIndex.find(_._1.id == id).map(_._2)

      index.getOrElse {
        scala.sys.error("Could not find '"+id+"' ("+id.uniqueName+") within "+fields.map(_.id.uniqueName).mkString(", "))
      }
    }
    
    lazy val singleCaseClasses : Seq[CaseClassDef] = if (hasParent) Nil else Seq(this)
    setSubDefOwners()
  }

 
  // Definition types (see below)
  object DefType extends Enumeration {
    type DefType = Value
    val MethodDef      = Value("def")
    val StrictFieldDef = Value("val")
    val LazyFieldDef   = Value("lazy val")
  } 
  import DefType._
  
  /** Functions
   *  This class represents methods or fields of objects (as specified by the defType field)
   *  that appear ONLY in the class/object's body (not the constructors)
   *  All of these are treated as functions for verification.
   *  Under circumstances (see canBeField and canBeLazyField methods) 
   *  they can be differentiated when it comes to code generation/pretty printing.
   *  
   *  Default type is DefDef (method)
   */
  class FunDef(
    val id: Identifier, 
    val tparams: Seq[TypeParameterDef], 
    val returnType: TypeTree, 
    val params: Seq[ValDef], 
    val defType : DefType
  ) extends Definition {
    
    // A copy of the original function before Xlang elimination
    var orig : Option[FunDef] = None
    
    private var fullBody_ : Expr = NoTree(returnType)
    def fullBody = fullBody_
    def fullBody_= (e : Expr) {
      fullBody_ = e
      nestedFuns map {_.setOwner(this)}
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

    def nestedFuns = directlyNestedFunDefs(fullBody)
    
    def subDefinitions = params ++ tparams ++ nestedFuns.toList

    def duplicate: FunDef = {
      val fd = new FunDef(id.freshen, tparams, returnType, params, defType)
      fd.copyContentFrom(this)
      fd.copiedFrom(this)
    }
    
    def copyContentFrom(from : FunDef) {
      this.fullBody  = from.fullBody 
      this.orig    = from.orig
      this.origOwner = from.origOwner
      this.addAnnotation(from.annotations.toSeq : _*)
    }

    def hasBody                     = body.isDefined
    def hasPrecondition : Boolean   = precondition.isDefined
    def hasPostcondition : Boolean  = postcondition.isDefined

    /**
     * When this functions has been annotated as a (lazy) field 
     * and has no arguments, it can be printed/compiled as a field 
     */
    def canBeLazyField   = defType == LazyFieldDef    && params.isEmpty && tparams.isEmpty
    def canBeStrictField = defType == StrictFieldDef  && params.isEmpty && tparams.isEmpty
    def canBeField       = canBeLazyField || canBeStrictField
    def isRealFunction   = !canBeField

    def isSynthetic = annotations contains "synthetic"
    
    private var annots: Set[String] = Set.empty[String]
    def addAnnotation(as: String*) : FunDef = {
      annots = annots ++ as
      this
    }
    def annotations : Set[String] = annots

    def isPrivate : Boolean = annots.contains("private")

    def typed(tps: Seq[TypeTree]) = {
      assert(tps.size == tparams.size)
      TypedFunDef(this, tps)
    }

    def typed = {
      assert(tparams.isEmpty)
      TypedFunDef(this, Nil)
    }

    def typedWithDef = {
      TypedFunDef(this, tparams.map(_.tp))
    }

    def isRecursive(p: Program) = p.callGraph.transitiveCallees(this) contains this

    setSubDefOwners()
    // Deprecated, old API
    @deprecated("Use .body instead", "2.3")
    def implementation : Option[Expr] = body

    @deprecated("Use .hasBody instead", "2.3")
    def hasImplementation : Boolean = hasBody

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
    private var postCache = Map[Expr, Expr]()

    def fullBody = {
      val fb = fd.fullBody
      trCache.getOrElse(fb, {
        val res = translated(fb)
        trCache += fb -> res
        res
      })
    }

    def body = fd.body.map { b =>
      trCache.getOrElse(b, {
        val res = translated(b)
        trCache += b -> res
        res
      })
    }

    def precondition = fd.precondition.map { pre =>
      trCache.getOrElse(pre, {
        val res = translated(pre)
        trCache += pre -> res
        res
      })
    }

    def postcondition = fd.postcondition.map {
      case post if typesMap.nonEmpty =>
        postCache.getOrElse(post, {
          val res = instantiateType(post, typesMap, paramsMap)
          postCache += (post -> res)
          res
        })

      case p => p
    }

    def hasImplementation = body.isDefined
    def hasBody           = hasImplementation
    def hasPrecondition   = precondition.isDefined
    def hasPostcondition  = postcondition.isDefined

    override def getPos = fd.getPos
  }
}
