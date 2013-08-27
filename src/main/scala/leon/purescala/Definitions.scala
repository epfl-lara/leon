/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package purescala

object Definitions {
  import Common._
  import Trees._
  import TreeOps._
  import Extractors._
  import TypeTrees._

  sealed abstract class Definition extends Serializable {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
    override def hashCode : Int = id.hashCode
    override def equals(that : Any) : Boolean = that match {
      case t : Definition => t.id == this.id
      case _ => false
    }
  }

  /** A VarDecl declares a new identifier to be of a certain type. */
  case class VarDecl(id: Identifier, tpe: TypeTree) extends Typed {
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
    def isCatamorphism(f1: FunDef) = mainObject.isCatamorphism(f1)
    def caseClassDef(name: String) = mainObject.caseClassDef(name)

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
    lazy val definedFunctions : Seq[FunDef] = defs.filter(_.isInstanceOf[FunDef]).map(_.asInstanceOf[FunDef])

    lazy val definedClasses : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef])

    def caseClassDef(caseClassName : String) : CaseClassDef =
    definedClasses.find(ctd => ctd.id.name == caseClassName).getOrElse(scala.sys.error("Asking for non-existent case class def: " + caseClassName)).asInstanceOf[CaseClassDef]

    lazy val classHierarchyRoots : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef]).filter(!_.hasParent)

    lazy val algebraicDataTypes : Map[AbstractClassDef,Seq[CaseClassDef]] = (defs.collect {
      case c @ CaseClassDef(_, Some(_), _) => c
    }).groupBy(_.parent.get)

    lazy val singleCaseClasses : Seq[CaseClassDef] = defs.collect {
      case c @ CaseClassDef(_, None, _) => c
    }

    lazy val (callGraph, callers, callees) = {
      type CallGraph = Set[(FunDef,FunDef)]

      val convert: Expr=>CallGraph = (_ => Set.empty)
      val combine: (CallGraph,CallGraph)=>CallGraph = (s1,s2) => s1 ++ s2
      def compute(fd: FunDef)(e: Expr, g: CallGraph) : CallGraph = e match {
        case f @ FunctionInvocation(f2, _) => g + ((fd, f2))
        case _ => g
      }

      val resSet: CallGraph = (for(funDef <- definedFunctions) yield {
        funDef.precondition.map(treeCatamorphism[CallGraph](convert, combine, compute(funDef)_, _)).getOrElse(Set.empty) ++
        funDef.body.map(treeCatamorphism[CallGraph](convert, combine, compute(funDef)_, _)).getOrElse(Set.empty) ++
        funDef.postcondition.map( pc => treeCatamorphism[CallGraph](convert, combine, compute(funDef)_, pc._2)).getOrElse(Set.empty)
      }).reduceLeft(_ ++ _)

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
  }

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassTypeDef extends Definition {
    self =>

    val id: Identifier
    def parent: Option[AbstractClassDef]
    def setParent(parent: AbstractClassDef) : self.type
    def hasParent: Boolean = parent.isDefined
    val isAbstract: Boolean

  }

  /** Will be used at some point as a common ground for case classes (which
   * implicitely define extractors) and explicitely defined unapply methods. */
  sealed trait ExtractorTypeDef 

  /** Abstract classes. */
  object AbstractClassDef {
    def unapply(acd: AbstractClassDef): Option[(Identifier,Option[AbstractClassDef])] = {
      if(acd == null) None else Some((acd.id, acd.parent))
    }
  }
  class AbstractClassDef(val id: Identifier, prnt: Option[AbstractClassDef] = None) extends ClassTypeDef {
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

    def setParent(newParent: AbstractClassDef) = {
      if(parent_.isDefined) {
        scala.sys.error("Resetting parent is forbidden.")
      }
      newParent.registerChild(this)
      parent_ = Some(newParent)
      this
    }
    def parent = parent_
  }

  /** Case classes. */
  object CaseClassDef {
    def unapply(ccd: CaseClassDef): Option[(Identifier,Option[AbstractClassDef],VarDecls)] =  {
      if(ccd == null) None else Some((ccd.id, ccd.parent, ccd.fields))
    }
  }

  class CaseClassDef(val id: Identifier, prnt: Option[AbstractClassDef] = None) extends ClassTypeDef with ExtractorTypeDef {
    private var parent_ = prnt
    var fields: VarDecls = Nil
    var isCaseObject = false
    val isAbstract = false

    def setParent(newParent: AbstractClassDef) = {
      if(parent_.isDefined) {
        scala.sys.error("Resetting parent is forbidden.")
      }
      newParent.registerChild(this)
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
  class FunDef(val id: Identifier, val returnType: TypeTree, val args: VarDecls) extends Definition with ScalacPositional {
    var body: Option[Expr] = None
    def implementation : Option[Expr] = body
    var precondition: Option[Expr] = None
    var postcondition: Option[(Identifier, Expr)] = None

    // Metadata kept here after transformations
    var parent: Option[FunDef] = None
    var orig: Option[FunDef] = None

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
}
