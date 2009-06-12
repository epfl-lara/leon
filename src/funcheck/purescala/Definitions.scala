package funcheck.purescala

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
  trait Scope {
    import scala.collection.immutable.Map

    def parentScope: Option[Scope] = None
    def lookupVar(id: Identifier): Option[VarDecl] = None
    def lookupObject(id: Identifier): Option[ObjectDef] = None
    def lookupClassType(id: Identifier): Option[ClassTypeDef] = None
    def lookupAbstractClass(id: Identifier): Option[AbstractClassDef] = None
    def lookupCaseClass(id: Identifier): Option[CaseClassDef] = None
    def lookupClass(id: Identifier): Option[ClassDef] = None
    def lookupFun(id: Identifier): Option[FunDef] = None
  }

  /** A declaration is anything "structural", ie. anything that's part of the
   * syntax of a program but not in an expression. */
  sealed abstract class Definition extends Scope {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
  }

  /** A VarDecl declares a new identifier to be of a certain type. */
  final case class VarDecl(id: Identifier, tpe: TypeTree) {
    val uniqueID: Int = UniqueID(id.toString)
    override val toString: String = id + uniqueID
    override def equals(other: Any) = other match {
      case v: VarDecl => this.equals(v) && uniqueID == v.uniqueID
      case _ => false
    }
  }

  type VarDecls = Seq[VarDecl]

  /** A wrapper for a program. For now a program is simply a single object. The
   * name is meaningless and we just use the package name. */
  final case class Program(id: Identifier, mainObject: ObjectDef) extends Definition {
    override val parentScope = None

    override def lookupObject(id: Identifier) = {
      if(id == mainObject.id) {
        Some(mainObject)
      } else {
        None
      }
    }
  }

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ObjectDef(id: Identifier, defs : Seq[Definition], invariants: Seq[Expr]) extends Definition 

  /** Useful because case classes and classes are somewhat unified in some
   * patterns (of pattern-matching, that is) */
  sealed trait ClassTypeDef extends Definition {
    val id: Identifier
    val parent: Option[AbstractClassDef]
    val fields: VarDecls
  }

  /** Will be used at some point as a common ground for case classes (which
   * implicitely define extractors) and explicitely defined unapply methods. */
  sealed trait ExtractorTypeDef

  /** Abstract classes. */
  case class AbstractClassDef(id: Identifier, parent: Option[AbstractClassDef], fields: VarDecls) extends ClassTypeDef

  /** Case classes. */
  case class CaseClassDef(id: Identifier, parent: Option[AbstractClassDef], fields: VarDecls) extends ClassTypeDef with ExtractorTypeDef

  /** "Regular" classes */
  case class ClassDef(id: Identifier, parent: Option[AbstractClassDef], fields: VarDecls) extends ClassTypeDef
  
  /** Values */
  case class ValDef(varDecl: VarDecl, value: Expr) extends Definition {
    val id: Identifier = varDecl.id
  }

  /** Functions (= 'methods' of objects) */
  case class FunDef(id: Identifier, args: VarDecls, body: Expr, precondition: Option[Expr], postcondition: Option[Expr]) extends Definition {
    lazy val argTypes : Seq[TypeTree] = args.map(_.tpe) 
    lazy val returnType : TypeTree = body.getType
  }
}
