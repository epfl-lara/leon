/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

object Definitions {
  import Common._
  import Trees._
  import TreeOps._
  import TypeTrees._
  import TypeTreeOps._
  import Extractors._

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
  case class VarDecl(id: Identifier, tpe: TypeTree) extends Definition with Typed {
    self: Serializable =>

    override def getType = tpe
    override def setType(tt: TypeTree) = scala.sys.error("Can't set type of VarDecl.")

    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : VarDecl => t.id == this.id
      case _ => false
    }

    def toVariable : Variable = Variable(id).setType(tpe)
  }

  type VarDecls = Seq[VarDecl]

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, mainObject: ObjectDef) extends Definition {
    def definedFunctions = mainObject.definedFunctions
    def definedClasses = mainObject.definedClasses
    def classHierarchyRoots = mainObject.classHierarchyRoots
    def algebraicDataTypes = mainObject.algebraicDataTypes
    def singleCaseClasses = mainObject.singleCaseClasses
    def callGraph = mainObject.callGraph
    def calls(f1: FunDef, f2: FunDef) = mainObject.calls(f1, f2)
    def callers(f1: FunDef) = mainObject.callers(f1)
    def callees(f1: FunDef) = mainObject.callees(f1)
    def transitiveCallGraph = mainObject.transitiveCallGraph
    def transitivelyCalls(f1: FunDef, f2: FunDef) = mainObject.transitivelyCalls(f1, f2)
    def transitiveCallers(f1: FunDef) = mainObject.transitiveCallers.getOrElse(f1, Set())
    def transitiveCallees(f1: FunDef) = mainObject.transitiveCallees.getOrElse(f1, Set())
    def isRecursive(f1: FunDef) = mainObject.isRecursive(f1)
    def caseClassDef(name: String) = mainObject.caseClassDef(name)
    def classes = mainObject.classes
    def roots = mainObject.roots

    def writeScalaFile(filename: String) {
      import java.io.FileWriter
      import java.io.BufferedWriter
      val fstream = new FileWriter(filename)
      val out = new BufferedWriter(fstream)
      out.write(ScalaPrinter(this))
      out.close
    }

    def duplicate = {
      copy(mainObject = mainObject.copy(defs = mainObject.defs.collect {
        case fd: FunDef => fd.duplicate
        case d => d
      }))
    }
  }

  object Program {
    lazy val empty : Program = Program(
      FreshIdentifier("empty"),
      ObjectDef(
        FreshIdentifier("empty"),
        Seq.empty,
        Seq.empty
      )
    )
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ObjectDef(id: Identifier, defs : Seq[Definition], invariants: Seq[Expr]) extends Definition {
    lazy val definedFunctions : Seq[FunDef] = defs.filter(_.isInstanceOf[FunDef]).map(_.asInstanceOf[FunDef]).sortBy(_.id.uniqueName)

    lazy val definedClasses : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef]).sortBy(_.id.uniqueName)

    def caseClassDef(caseClassName : String) : CaseClassDef =
    definedClasses.find(ctd => ctd.id.name == caseClassName).getOrElse(scala.sys.error("Asking for non-existent case class def: " + caseClassName)).asInstanceOf[CaseClassDef]

    lazy val classHierarchyRoots : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef]).filter(!_.hasParent)

    lazy val algebraicDataTypes : Map[AbstractClassDef,Seq[CaseClassDef]] = (defs.collect {
      case c @ CaseClassDef(_, _, Some(_), _) => c
    }).groupBy(_.parent.get.classDef)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c @ CaseClassDef(_, _, None, _) => c
    }

    lazy val (callGraph, callers, callees) = {
      type CallGraph = Set[(FunDef,FunDef)]

      def collectCalls(fd: FunDef)(e: Expr): CallGraph = e match {
        case f @ FunctionInvocation(f2, _) => Set((fd, f2))
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

    def isCatamorphism(f : FunDef) : Boolean = {
      val c = callees(f)
      if(f.hasImplementation && f.args.size == 1 && c.size == 1 && c.head == f) f.body.get match {
        case SimplePatternMatching(scrut, _, _) if (scrut == f.args.head.toVariable) => true
        case _ => false
      } else {
        false
      }
    }

    lazy val types = {
      val exprs = definedFunctions.flatMap { funDef =>
        funDef.args.map(_.toVariable) ++
        funDef.precondition ++
        funDef.body ++
        funDef.postcondition.map(_._2)
      }

      exprs.flatMap(transitiveTypes(_)).toSet
    }

    lazy val roots : Seq[ClassType] = types.collect { case (ct : ClassType) if !ct.classDef.hasParent => ct }.toSeq

    lazy val classes : Seq[ClassType] = roots.flatMap(_ match {
      case (act : AbstractClassType) => Seq(act) ++ act.knownChildren
      case (cct : CaseClassType) => Seq(cct)
    })
  }

  sealed case class TypeParameterDef(id: Identifier) {
    def toType: TypeParameter = TypeParameter(id)
  }

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassTypeDef extends Definition {
    self =>

    val id: Identifier
    val tparams: Seq[TypeParameterDef]
    def parent: Option[AbstractClassType]
    def setParent(parent: AbstractClassType) : self.type
    def hasParent: Boolean = parent.isDefined
    val isAbstract: Boolean
  }

  /** Will be used at some point as a common ground for case classes (which
   * implicitely define extractors) and explicitely defined unapply methods. */
  sealed trait ExtractorTypeDef 

  /** Abstract classes. */
  object AbstractClassDef {
    def unapply(acd: AbstractClassDef): Option[(Identifier,Seq[TypeParameterDef],Option[AbstractClassType])] = {
      if(acd == null) None else Some((acd.id, acd.tparams, acd.parent))
    }
  }
  class AbstractClassDef(val id: Identifier, val tparams: Seq[TypeParameterDef], prnt: Option[AbstractClassType] = None) extends ClassTypeDef {
    private var parent_ = prnt
    var fields: VarDecls = Nil
    val isAbstract = true

    private var children : List[ClassTypeDef] = Nil

    private[purescala] def registerChild(child: ClassTypeDef) : Unit = {
      children = child :: children
    }

    def knownChildren : Seq[ClassTypeDef] = {
      children
    }

    def knownDescendents : Seq[ClassTypeDef] = {
      knownChildren ++ (knownChildren.map(c => c match {
        case acd: AbstractClassDef => acd.knownDescendents
        case _ => Nil
      }).reduceLeft(_ ++ _))
    }

    def setParent(newParent: AbstractClassType) = {
      if(parent_.isDefined) {
        scala.sys.error("Resetting parent is forbidden.")
      }
      newParent.classDef.registerChild(this)
      parent_ = Some(newParent)
      this
    }
    def parent = parent_
  }

  /** Case classes. */
  object CaseClassDef {
    def unapply(ccd: CaseClassDef): Option[(Identifier,Seq[TypeParameterDef],Option[AbstractClassType],VarDecls)] =  {
      if(ccd == null) None else Some((ccd.id, ccd.tparams, ccd.parent, ccd.fields))
    }
  }

  class CaseClassDef(val id: Identifier, val tparams: Seq[TypeParameterDef], prnt: Option[AbstractClassType] = None) extends ClassTypeDef with ExtractorTypeDef {
    private var parent_ = prnt
    var fields: VarDecls = Nil
    var isCaseObject = false
    val isAbstract = false

    def setParent(newParent: AbstractClassType) = {
      if(parent_.isDefined) {
        scala.sys.error("Resetting parent is forbidden.")
      }
      newParent.classDef.registerChild(this)
      parent_ = Some(newParent)
      this
    }
    def parent = parent_

    def fieldsIds = fields.map(_.id)

    def selectorID2Index(id: Identifier) : Int = {
      var i : Int = 0
      var found = false
      val fs = fields.size
      while(!found && i < fs) {
        if(fields(i).id == id) {
          found = true
        } else {
          i += 1
        }
      }

      if(found)
        i
      else
        scala.sys.error("Asking for index of field that does not belong to the case class.")
    }
  }

  /** Values */
  case class ValDef(varDecl: VarDecl, value: Expr) extends Definition {
    val id: Identifier = varDecl.id
  }

  /** Functions (= 'methods' of objects) */
  class FunDef(val id: Identifier, val tparams: Seq[TypeParameterDef], val returnType: TypeTree, val args: VarDecls) extends Definition {
    def this(id: Identifier, returnType: TypeTree, args: VarDecls) = this(id,
      (returnType +: args.map(_.tpe)).flatMap(collectParametricTypes).toSeq.map(TypeParameterDef(_)),
      returnType,
      args)

    var body: Option[Expr] = None
    def implementation : Option[Expr] = body
    var precondition: Option[Expr] = None
    var postcondition: Option[(Identifier, Expr)] = None

    // Metadata kept here after transformations
    var parent: Option[FunDef] = None
    var orig: Option[FunDef] = None

    def duplicate: FunDef = {
      val fd = new FunDef(id, returnType, args)
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
  }

  object TypedFunDef {
    private def typed(fd: FunDef, tparams: Seq[TypeTree], isRealFunDef: Boolean): TypedFunDef = {
      assert(fd.tparams.size == tparams.size)
      val hoistedParams = tparams.map(tp => searchAndReplaceTypesDFS({
        case cct @ CaseClassType(_, _) => cct.parent
        case _ => None
      })(tp))

      new TypedFunDef(fd, hoistedParams, isRealFunDef)
    }

    def apply(fd: FunDef, tparams: Seq[TypeTree]): TypedFunDef = typed(fd, tparams, true)

    def apply(fd: FunDef, isRealFunDef: Boolean = true): TypedFunDef = typed(fd, fd.tparams.map(_.toType), isRealFunDef)

    def unapply(tfd: TypedFunDef): Option[(FunDef, Seq[TypeTree])] = {
      if (tfd == null) None else Some((tfd.fd, tfd.tparams))
    }
  }

  class TypedFunDef private(val fd: FunDef, val tparams: Seq[TypeTree], isRealFunDef: Boolean = true) {
    private val typeMapping : Map[TypeParameter, TypeTree] = Map(fd.tparams.map(_.toType) zip tparams : _*)

    private val id2typed : Map[Identifier, Identifier] = if (isRealFunDef) {
      fd.args.map { case VarDecl(id, tpe) => id -> id.freshenWithType(replaceTypesFromTPs(typeMapping.get _, tpe)) }.toMap
    } else {
      fd.args.map(vd => vd.id -> vd.id).toMap
    }

    private val id2var : Map[Identifier, Expr] = id2typed.mapValues(_.toVariable)

    val id : Identifier = fd.id
    val args : VarDecls = fd.args.map { case VarDecl(id, tpe) =>
      val newID = id2typed(id)
      VarDecl(newID, newID.getType)
    }

    val returnType : TypeTree = replaceTypesFromTPs(typeMapping.get _, fd.returnType)

    def hasImplementation = fd.hasImplementation
    def hasPrecondition = fd.hasPrecondition
    def hasPostcondition = fd.hasPostcondition
    def hasBody = fd.hasBody

    def precondition : Option[Expr] = fd.precondition.map(prec => replaceTypesInExpr(typeMapping, id2var, prec))
    def body : Option[Expr] = fd.body.map(body => replaceTypesInExpr(typeMapping, id2var, body))
    def postcondition : Option[(Identifier,Expr)] = fd.postcondition.map { case (id, post) =>
      val newID = id.freshenWithType(replaceTypesFromTPs(typeMapping.get _, id.getType))
      newID -> replaceTypesInExpr(typeMapping, id2var + (id -> newID.toVariable), post)
    }

    override def equals(obj: Any): Boolean = obj match {
      case (tfd: TypedFunDef) => (tfd.fd, tfd.tparams) == (fd, tparams)
      case _ => false
    }
    
    override def hashCode : Int = (fd, tparams).hashCode

    override def toString : String = fd.id + tparams.mkString("[",",","]")
  }
}
