/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

object Definitions {
  import Common._
  import Trees._
  import TreeOps._
  import Extractors._
  import TypeTrees._
  import TypeTreeOps._

  sealed abstract class Definition extends Tree {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }
  }

  /** A VarDecl declares a new identifier to be of a certain type. */
  case class VarDecl(id: Identifier, tpe: TypeTree) extends Definition with FixedType {
    self: Serializable =>

    val fixedType = tpe

    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : VarDecl => t.id == this.id
      case _ => false
    }

    def toVariable : Variable = Variable(id).setType(tpe)
  }

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, mainModule: ModuleDef) extends Definition {
    def definedFunctions = mainModule.definedFunctions
    def definedClasses   = mainModule.definedClasses
    def classHierarchyRoots = mainModule.classHierarchyRoots
    def algebraicDataTypes = mainModule.algebraicDataTypes
    def singleCaseClasses = mainModule.singleCaseClasses
    def callGraph = mainModule.callGraph

    def calls(f1: FunDef, f2: FunDef) = mainModule.calls(f1, f2)
    def callers(f1: FunDef) = mainModule.callers(f1)
    def callees(f1: FunDef) = mainModule.callees(f1)
    def transitiveCallGraph = mainModule.transitiveCallGraph
    def transitivelyCalls(f1: FunDef, f2: FunDef) = mainModule.transitivelyCalls(f1, f2)
    def transitiveCallers(f1: FunDef) = mainModule.transitiveCallers.getOrElse(f1, Set())
    def transitiveCallees(f1: FunDef) = mainModule.transitiveCallees.getOrElse(f1, Set())
    def isRecursive(f1: FunDef) = mainModule.isRecursive(f1)
    def caseClassDef(name: String) = mainModule.caseClassDef(name)

    def writeScalaFile(filename: String) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this))
      out.close
    }

    def duplicate = {
      copy(mainModule = mainModule.copy(defs = mainModule.defs.collect {
        case fd: FunDef => fd.duplicate
        case d => d
      }))
    }
  }

  object Program {
    lazy val empty : Program = Program(
      FreshIdentifier("empty"),
      ModuleDef(
        FreshIdentifier("empty"),
        Seq.empty,
        Seq.empty
      )
    )
  }

  case class TypeParameterDef(tp: TypeParameter) extends Definition {
    val id = tp.id
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ModuleDef(id: Identifier, defs : Seq[Definition], invariants: Seq[Expr]) extends Definition {
    lazy val definedFunctions : Seq[FunDef] = defs.collect { case fd: FunDef => fd }

    lazy val definedClasses : Seq[ClassDef] = defs.collect { case ctd: ClassDef => ctd }

    def caseClassDef(name : String) : CaseClassDef = definedClasses.find(ctd => ctd.id.name == name) match {
      case Some(ccd: CaseClassDef) => ccd
      case _ => throw new LeonFatalError("Unknown case class '"+name+"'")
    }

    lazy val classHierarchyRoots : Seq[ClassDef] = defs.collect {
      case ctd: ClassDef if !ctd.hasParent => ctd
    }

    lazy val algebraicDataTypes : Map[AbstractClassDef, Seq[CaseClassDef]] = (defs.collect {
      case c @ CaseClassDef(_, _, Some(p), _) => c
    }).groupBy(_.parent.get.classDef)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c @ CaseClassDef(_, _, None, _) => c
    }

    lazy val (callGraph, callers, callees) = {
      type CallGraph = Set[(FunDef,FunDef)]

      def collectCalls(fd: FunDef)(e: Expr): CallGraph = e match {
        case f @ FunctionInvocation(f2, _) => Set((fd, f2.fd))
        case _ => Set()
      }

      val resSet: CallGraph = (for(funDef <- definedFunctions) yield {
        funDef.precondition.map(collect(collectCalls(funDef))(_)).getOrElse(Set()) ++
        funDef.body.map(collect(collectCalls(funDef))(_)).getOrElse(Set()) ++
        funDef.postcondition.map(p => collect(collectCalls(funDef))(p._2)).getOrElse(Set())
      }).foldLeft(Set[(FunDef, FunDef)]())(_ ++ _)

      var callers: Map[FunDef,Set[FunDef]] =
        new scala.collection.immutable.HashMap[FunDef,Set[FunDef]]
      var callees: Map[FunDef,Set[FunDef]] =
        new scala.collection.immutable.HashMap[FunDef,Set[FunDef]]

      for(funDef <- definedFunctions) {
        val clrs = resSet.filter(_._2 == funDef).map(_._1)
        val cles = resSet.filter(_._1 == funDef).map(_._2)
        callers = callers + (funDef -> clrs)
        callees = callees + (funDef -> cles)
      }

      (resSet, callers, callees)
    }

    // checks whether f1's body, pre or post contain calls to f2
    def calls(f1: FunDef, f2: FunDef) : Boolean = callGraph((f1,f2))

    lazy val (transitiveCallGraph, transitiveCallers, transitiveCallees) = {
      var tCallees: Map[FunDef, Set[FunDef]] = callGraph.groupBy(_._1).mapValues(_.map(_._2).toSet)
      var change = true

      while(change) {
        change = false
        for ((fd, calls) <- tCallees) {
          val newCalls = calls ++ calls.flatMap(tCallees.getOrElse(_, Set()))

          if (newCalls != calls) {
            change = true
            tCallees += fd -> newCalls
          }
        }
      }

      val tCallGraph: Set[(FunDef, FunDef)] = tCallees.toSeq.flatMap {
        case (fd, calls) => calls.map(fd -> _)
      }.toSet

      val tCallers: Map[FunDef, Set[FunDef]] = tCallGraph.groupBy(_._2).mapValues(_.map(_._1).toSet)

      (tCallGraph, tCallers, tCallees)
    }

    def transitivelyCalls(f1: FunDef, f2: FunDef) : Boolean = transitiveCallGraph((f1,f2))

    def isRecursive(f: FunDef) = transitivelyCalls(f, f)
  }

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassDef extends Definition {
    self =>

    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    def fields: Seq[VarDecl]
    val parent: Option[AbstractClassType]

    def hasParent = parent.isDefined

    def fieldsIds = fields.map(_.id)

    private var _children: List[ClassDef] = Nil

    def registerChildren(chd: ClassDef) = {
      _children = (chd :: _children).sortBy(_.id.name)
    }

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

    var _fields = Seq[VarDecl]()

    def fields = _fields

    def setFields(fields: Seq[VarDecl]) {
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

  /** Values */
  case class ValDef(varDecl: VarDecl, value: Expr) extends Definition {
    val id: Identifier = varDecl.id
  }

  /** Functions (= 'methods' of objects) */
  class FunDef(val id: Identifier, val tparams: Seq[TypeParameterDef], val returnType: TypeTree, val args: Seq[VarDecl]) extends Definition {
    var body: Option[Expr] = None
    def implementation : Option[Expr] = body
    var precondition: Option[Expr] = None
    var postcondition: Option[(Identifier, Expr)] = None

    // Metadata kept here after transformations
    var parent: Option[FunDef] = None
    var orig: Option[FunDef] = None

    def duplicate: FunDef = {
      val fd = new FunDef(id, tparams, returnType, args)
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

    def translated(e: Expr): Expr = instantiateType(e, typesMap, argsMap)

    lazy val (args: Seq[VarDecl], argsMap: Map[Identifier, Identifier]) = {
      if (typesMap.isEmpty) {
        (fd.args, Map())
      } else {
        val newArgs = fd.args.map {
          case vd @ VarDecl(id, tpe) =>
            val newTpe = translated(tpe)
            val newId = FreshIdentifier(id.name, true).setType(newTpe).copiedFrom(id)

            VarDecl(newId, newTpe).setPos(vd)
        }

        val argsMap: Map[Identifier, Identifier] = (fd.args zip newArgs).map { case (vd1, vd2) => vd1.id -> vd2.id }.toMap

        (newArgs, argsMap)
      }
    }

    lazy val functionType = FunctionType(args.map(_.tpe).toList, returnType)

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
          val res = nId -> instantiateType(post, typesMap, argsMap + (id -> nId))
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
