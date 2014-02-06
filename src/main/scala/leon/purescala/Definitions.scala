/* Copyright 2009-2013 EPFL, Lausanne */

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
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }
  }

  /** A ValDef declares a new identifier to be of a certain type. */
  case class ValDef(id: Identifier, tpe: TypeTree) extends Definition with FixedType {
    self: Serializable =>

    val fixedType = tpe

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
  }

  object Program {
    lazy val empty : Program = Program(
      FreshIdentifier("empty"),
      Nil
    )
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    val id = tp.id
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(id: Identifier, defs : Seq[Definition]) extends Definition {
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
      }).reduceLeft(_ ++ _))
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

  /** Functions (= 'methods' of objects) */
  class FunDef(val id: Identifier, val tparams: Seq[TypeParameterDef], val returnType: TypeTree, val params: Seq[ValDef]) extends Definition {
    var body: Option[Expr] = None
    def implementation : Option[Expr] = body
    var precondition: Option[Expr] = None
    var postcondition: Option[(Identifier, Expr)] = None

    // Metadata kept here after transformations
    var parent: Option[FunDef] = None
    var orig: Option[FunDef] = None

    def duplicate: FunDef = {
      val fd = new FunDef(id, tparams, returnType, params)
      fd.body = body
      fd.precondition = precondition
      fd.postcondition = postcondition
      fd.parent = parent
      fd.orig = orig
      fd
    }

    def hasImplementation : Boolean = body.isDefined
    def hasBody                     = hasImplementation
    def hasPrecondition : Boolean   = precondition.isDefined
    def hasPostcondition : Boolean  = postcondition.isDefined

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
