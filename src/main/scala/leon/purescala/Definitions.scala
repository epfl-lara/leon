/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package purescala

import scala.collection.generic.CanBuildFrom

object Definitions {
  import Common._
  import Trees._
  import TreeOps._
  import Extractors._
  import TypeTrees._
  import TypeTreeOps._

  sealed abstract class Definition extends Tree {
    val id: Identifier
    var enclosing : Option[Definition] = None // The definition/scope enclosing this definition
    def subDefinitions : Seq[Definition]      // The enclosed scopes/definitions by this definition
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }
    override def copiedFrom(o : Tree) : this.type = {
      super.copiedFrom(o)
      o match {
        case df : Definition => enclosing = df.enclosing
        case _ => // FIXME should this ever happen?
      }
      this
    }

  }

  /** A ValDef declares a new identifier to be of a certain type. */
  case class ValDef(id: Identifier, tpe: TypeTree) extends Definition with FixedType {
    self: Serializable =>

    val fixedType = tpe

    def subDefinitions = Seq()
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : ValDef => t.id == this.id
      case _ => false
    }

    def toVariable : Variable = Variable(id).setType(tpe)
  }

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, modules: List[ModuleDef]) extends Definition {
    enclosing = None
    def subDefinitions = modules
    
    def definedFunctions    = modules.flatMap(_.definedFunctions)
    def definedClasses      = modules.flatMap(_.definedClasses)
    def classHierarchyRoots = modules.flatMap(_.classHierarchyRoots)
    def algebraicDataTypes  = modules.flatMap(_.algebraicDataTypes).toMap
    def singleCaseClasses   = modules.flatMap(_.singleCaseClasses)

    lazy val callGraph      = new CallGraph(this)

    def caseClassDef(name: String) = definedClasses.collect {
      case ccd: CaseClassDef if ccd.id.name == name => ccd
    }.headOption.getOrElse(throw LeonFatalError("Unknown case class '"+name+"'"))

    def duplicate = {
      copy(modules = modules.map(m => m.copy(defs = m.defs.collect {
        case fd: FunDef => fd.duplicate
        case d => d
      })))
    }
    
    def writeScalaFile(filename: String) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this))
      out.close
    }
  }

  object Program {
    lazy val empty : Program = Program(
      FreshIdentifier("empty"),
      Nil
    )
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    def subDefinitions = Seq()
    val id = tp.id
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(id: Identifier, defs : Seq[Definition]) extends Definition {
    
    def subDefinitions = defs
    
    lazy val definedFunctions : Seq[FunDef] = defs.collect { case fd: FunDef => fd }

    lazy val definedClasses : Seq[ClassDef] = defs.collect { case ctd: ClassDef => ctd }

    lazy val classHierarchyRoots : Seq[ClassDef] = defs.collect {
      case ctd: ClassDef if !ctd.hasParent => ctd
    }

    lazy val algebraicDataTypes : Map[AbstractClassDef, Seq[CaseClassDef]] = (defs.collect {
      case c @ CaseClassDef(_, _, Some(p), _) => c
    }).groupBy(_.parent.get.classDef)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c @ CaseClassDef(_, _, None, _) => c
    }

  }

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassDef extends Definition {
    self =>

    def subDefinitions = methods
      
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
    }

    def clearMethods() {
      _methods = Nil
    }

    def methods = _methods.toList

    def knownChildren: Seq[ClassDef] = _children

    def knownDescendents: Seq[ClassDef] = {
      knownChildren ++ (knownChildren.map(c => c match {
        case acd: AbstractClassDef => acd.knownDescendents
        case _ => Nil
      }).foldLeft(List[ClassDef]())(_ ++ _))
    }

    def knownCCDescendents: Seq[CaseClassDef] = knownDescendents.collect {
      case ccd: CaseClassDef =>
        ccd
    }

    val isAbstract: Boolean
    val isCaseObject: Boolean
  }

  /** Abstract classes. */
  case class AbstractClassDef(val id: Identifier,
                              val tparams: Seq[TypeParameterDef],
                              val parent: Option[AbstractClassType]) extends ClassDef {

    val fields = Nil
    val isAbstract   = true
    val isCaseObject = false
  }

  /** Case classes/objects. */
  case class CaseClassDef(val id: Identifier,
                          val tparams: Seq[TypeParameterDef],
                          val parent: Option[AbstractClassType],
                          val isCaseObject: Boolean) extends ClassDef {

    var _fields = Seq[ValDef]()

    def fields = _fields

    def setFields(fields: Seq[ValDef]) {
      _fields = fields
    }


    val isAbstract = false


    def selectorID2Index(id: Identifier) : Int = {
      val index = fields.zipWithIndex.find(_._1.id == id).map(_._2)

      index.getOrElse {
        scala.sys.error("Could not find '"+id+"' ("+id.uniqueName+") within "+fields.map(_.id.uniqueName).mkString(", "))
      }
    }
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
    
    var fullBody: Expr = NoTree(returnType)

    def body: Option[Expr] = withoutSpec(fullBody)
    def body_=(b: Option[Expr]) = fullBody = withBody(fullBody, b)

    def precondition = preconditionOf(fullBody)
    def precondition_=(oe: Option[Expr]) = {
      fullBody = withPrecondition(fullBody, oe)
    }

    def postcondition = postconditionOf(fullBody)
    def postcondition_=(op: Option[(Identifier, Expr)]) = {
      fullBody = withPostcondition(fullBody, op)
    }

    def subDefinitions = Seq()

    // Metadata kept here after transformations
    var parent: Option[FunDef] = None
    var orig: Option[FunDef] = None

    def duplicate: FunDef = {
      val fd = new FunDef(id, tparams, returnType, params, defType)
      fd.copyContentFrom(this)
      fd.copiedFrom(this)
    }
    
    def copyContentFrom(from : FunDef) {
      this.fullBody       = from.fullBody
      this.parent         = from.parent
      this.orig           = from.orig
      this.enclosing      = from.enclosing
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

    private lazy val typesMap = {
      (fd.tparams zip tps).toMap.filter(tt => tt._1 != tt._2)
    }

    def translated(t: TypeTree): TypeTree = instantiateType(t, typesMap)

    def translated(e: Expr): Expr = instantiateType(e, typesMap, paramsMap)

    lazy val (params: Seq[ValDef], paramsMap: Map[Identifier, Identifier]) = {
      if (typesMap.isEmpty) {
        (fd.params, Map())
      } else {
        val newParams = fd.params.map {
          case vd @ ValDef(id, tpe) =>
            val newTpe = translated(tpe)
            val newId = FreshIdentifier(id.name, true).setType(newTpe).copiedFrom(id)

            ValDef(newId, newTpe).setPos(vd)
        }

        val paramsMap: Map[Identifier, Identifier] = (fd.params zip newParams).map { case (vd1, vd2) => vd1.id -> vd2.id }.toMap

        (newParams, paramsMap)
      }
    }

    lazy val functionType = FunctionType(params.map(_.tpe).toList, returnType)

    lazy val returnType: TypeTree = translated(fd.returnType)

    private var trCache = Map[Expr, Expr]()
    private var postCache = Map[(Identifier, Expr), (Identifier, Expr)]()

    def body          = fd.body.map { b =>
      trCache.getOrElse(b, {
        val res = translated(b)
        trCache += b -> res
        res
      })
    }

    def precondition  = fd.precondition.map { pre =>
      trCache.getOrElse(pre, {
        val res = translated(pre)
        trCache += pre -> res
        res
      })
    }

    def postcondition = fd.postcondition.map {
      case (id, post) if typesMap.nonEmpty =>
        postCache.getOrElse((id, post), {
          val nId = FreshIdentifier(id.name).setType(translated(id.getType)).copiedFrom(id)
          val res = nId -> instantiateType(post, typesMap, paramsMap + (id -> nId))
          postCache += ((id,post) -> res)
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
