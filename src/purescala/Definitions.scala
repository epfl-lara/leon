package purescala

object Definitions {
  import Common._
  import Trees._
  import TypeTrees._

  sealed abstract class Definition {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
  }

  /** A VarDecl declares a new identifier to be of a certain type. */
  case class VarDecl(id: Identifier, tpe: TypeTree) extends Typed {
    override def getType = tpe
    override def setType(tt: TypeTree) = scala.Predef.error("Can't set type of VarDecl.")

    def toVariable : Variable = Variable(id).setType(tpe)
  }

  type VarDecls = Seq[VarDecl]

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, mainObject: ObjectDef) extends Definition {
    def definedFunctions = mainObject.definedFunctions
    def definedClasses = mainObject.definedClasses
    def classHierarchyRoots = mainObject.classHierarchyRoots
    def callGraph = mainObject.callGraph
    def calls(f1: FunDef, f2: FunDef) = mainObject.calls(f1, f2)
    def callers(f1: FunDef) = mainObject.callers(f1)
    def callees(f1: FunDef) = mainObject.callees(f1)
    def transitiveCallGraph = mainObject.transitiveCallGraph
    def transitivelyCalls(f1: FunDef, f2: FunDef) = mainObject.transitivelyCalls(f1, f2)
    def transitiveCallers(f1: FunDef) = mainObject.transitiveCallers(f1)
    def transitiveCallees(f1: FunDef) = mainObject.transitiveCallees(f1)
    def isRecursive(f1: FunDef) = mainObject.isRecursive(f1)
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ObjectDef(id: Identifier, defs : Seq[Definition], invariants: Seq[Expr]) extends Definition {
    lazy val definedFunctions : Seq[FunDef] = defs.filter(_.isInstanceOf[FunDef]).map(_.asInstanceOf[FunDef])

    lazy val definedClasses : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef])

    lazy val classHierarchyRoots : Seq[ClassTypeDef] = defs.filter(_.isInstanceOf[ClassTypeDef]).map(_.asInstanceOf[ClassTypeDef]).filter(!_.hasParent)

    lazy val (callGraph, callers, callees) = {
      var resSet: Set[(FunDef,FunDef)] =
        new scala.collection.immutable.HashSet[(FunDef,FunDef)]()

      def isFunCall(e: Expr) : Boolean = e.isInstanceOf[FunctionInvocation]
      def applyToFunCall(f1: FunDef)(e: Expr) : Expr = e match {
        case f @ FunctionInvocation(f2, _) => { resSet = resSet + ((f1,f2)); f }
        case o => o
      }

      for(funDef <- definedFunctions) {
        funDef.precondition.map(searchAndApply(isFunCall, applyToFunCall(funDef), _))
        funDef.body.map(searchAndApply(isFunCall, applyToFunCall(funDef), _))
        funDef.postcondition.map(searchAndApply(isFunCall, applyToFunCall(funDef), _))
      }

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
      var resSet : Set[(FunDef,FunDef)] = callGraph
      var change = true

      while(change) {
        change = false
        for(f1 <- definedFunctions; f2 <- callers(f1); f3 <- callees(f1)) {
          if(!resSet(f2,f3)) {
            change = true
            resSet = resSet + ((f2,f3))
          }
        }
      }

      var tCallers: Map[FunDef,Set[FunDef]] =
        new scala.collection.immutable.HashMap[FunDef,Set[FunDef]]
      var tCallees: Map[FunDef,Set[FunDef]] =
        new scala.collection.immutable.HashMap[FunDef,Set[FunDef]]

      for(funDef <- definedFunctions) {
        val clrs = resSet.filter(_._2 == funDef).map(_._1)
        val cles = resSet.filter(_._1 == funDef).map(_._2)
        tCallers = tCallers + (funDef -> clrs)
        tCallees = tCallees + (funDef -> cles)
      }

      (resSet, tCallers, tCallees)
    }

    def transitivelyCalls(f1: FunDef, f2: FunDef) : Boolean = transitiveCallGraph((f1,f2))

    def isRecursive(f: FunDef) = transitivelyCalls(f, f)
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
        scala.Predef.error("Resetting parent is forbidden.")
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
    val isAbstract = false

    def setParent(newParent: AbstractClassDef) = {
      if(parent_.isDefined) {
        scala.Predef.error("Resetting parent is forbidden.")
      }
      newParent.registerChild(this)
      parent_ = Some(newParent)
      this
    }
    def parent = parent_
  }

  /** "Regular" classes */
  //class ClassDef(val id: Identifier, var parent: Option[AbstractClassDef]) extends ClassTypeDef {
  //  var fields: VarDecls = Nil
  //  val isAbstract = false
  //}
  
  /** Values */
  case class ValDef(varDecl: VarDecl, value: Expr) extends Definition {
    val id: Identifier = varDecl.id
  }

  /** Functions (= 'methods' of objects) */
  object FunDef {
    def unapply(fd: FunDef): Option[(Identifier,TypeTree,VarDecls,Option[Expr],Option[Expr],Option[Expr])] = {
      if(fd != null) {
        Some((fd.id, fd.returnType, fd.args, fd.body, fd.precondition, fd.postcondition))
      } else {
        None
      }
    }
  }
  class FunDef(val id: Identifier, val returnType: TypeTree, val args: VarDecls) extends Definition {
    var body: Option[Expr] = None
    var precondition: Option[Expr] = None
    var postcondition: Option[Expr] = None

    def hasImplementation : Boolean = body.isDefined
    def hasPrecondition : Boolean = precondition.isDefined
    def hasPostcondition : Boolean = postcondition.isDefined
  }
}
