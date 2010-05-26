package purescala

object Definitions {
  import Common._
  import Trees._
  import TypeTrees._

  private object UniqueID {
    import scala.collection.mutable.HashMap

    private val counts: HashMap[String,Int] = new HashMap[String,Int]

    def apply(prefix: String): Int = {
      val count = counts.getOrElse(prefix, 0)
      counts(prefix) = count + 1
      count
    }
  }

  /** Scopes add new definitions to the surrounding scope. */
  // trait Scope {
  //   import scala.collection.immutable.Map

  //   def parentScope: Option[Scope] = None
  //   def lookupVar(id: Identifier): Option[VarDecl] = None
  //   def lookupObject(id: Identifier): Option[ObjectDef] = None
  //   def lookupClassType(id: Identifier): Option[ClassTypeDef] = None
  //   def lookupAbstractClass(id: Identifier): Option[AbstractClassDef] = None
  //   def lookupCaseClass(id: Identifier): Option[CaseClassDef] = None
  //   def lookupClass(id: Identifier): Option[ClassDef] = None
  //   def lookupFun(id: Identifier): Option[FunDef] = None
  // }

  /** A declaration is anything "structural", ie. anything that's part of the
   * syntax of a program but not in an expression. */
  sealed abstract class Definition /*extends Scope*/ {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
  }

  /** A VarDecl declares a new identifier to be of a certain type. */
  case class VarDecl(id: Identifier, tpe: TypeTree) extends Typed {
    val uniqueID: Int = UniqueID(id.toString)

    override val toString: String = id + uniqueID

    override def equals(other: Any) = other match {
      case v: VarDecl => this.equals(v) && uniqueID == v.uniqueID
      case _ => false
    }

    override def getType = tpe
    override def setType(tt: TypeTree) = scala.Predef.error("Can't set type of VarDecl.")
  }

  type VarDecls = Seq[VarDecl]

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name as id. */
  case class Program(id: Identifier, mainObject: ObjectDef) extends Definition {
    //override val parentScope = None

    // override def lookupObject(id: Identifier) = {
    //   if(id == mainObject.id) {
    //     Some(mainObject)
    //   } else {
    //     None
    //   }
    // }
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ObjectDef(id: Identifier, defs : Seq[Definition], invariants: Seq[Expr]) extends Definition 

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassTypeDef extends Definition {
    val id: Identifier
    var parent: Option[AbstractClassDef]
    val isAbstract: Boolean
    // val fields: VarDecls
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
  class AbstractClassDef(val id: Identifier, var parent: Option[AbstractClassDef]) extends ClassTypeDef {
    var fields: VarDecls = Nil
    val isAbstract = true
  }

  /** Case classes. */
  object CaseClassDef {
    def unapply(ccd: CaseClassDef): Option[(Identifier,Option[AbstractClassDef],VarDecls)] =  {
      if(ccd == null) None else Some((ccd.id, ccd.parent, ccd.fields))
    }
  }
  class CaseClassDef(val id: Identifier, var parent: Option[AbstractClassDef]) extends ClassTypeDef with ExtractorTypeDef {
    var fields: VarDecls = Nil
    val isAbstract = false
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
    def unapply(fd: FunDef): Option[(Identifier,TypeTree,VarDecls,Expr,Option[Expr],Option[Expr])] = {
      if(fd != null) {
        Some((fd.id, fd.returnType, fd.args, fd.body, fd.precondition, fd.postcondition))
      } else {
        None
      }
    }
  }
  class FunDef(val id: Identifier, val returnType: TypeTree, val args: VarDecls) extends Definition {
    var body: Expr = _
    var precondition: Option[Expr] = None
    var postcondition: Option[Expr] = None
  }
}
