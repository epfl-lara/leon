package funcheck.purescala

object Definitions {
  import Common._
  import Trees._
  import TypeTrees._

  sealed abstract class Definition {
    val id: Identifier
    override def toString: String = PrettyPrinter(this)
  }

  final case class VarDecl(id: Identifier, tpe: TypeTree)
  type VarDecls = Seq[VarDecl]

  /** Objects work as containers for class definitions, functions (def's) and
   * val's. */
  case class ObjectDef(id: Identifier, defs : Seq[Definition]) extends Definition

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
  case class ValDef(id: Identifier, value: Expr) extends Definition

  /** Functions (= 'methods' of objects) */
  case class FunDef(id: Identifier, args: VarDecls, body: Expr) extends Definition {
    lazy val argTypes : Seq[TypeTree] = args.map(_.tpe) 
    lazy val returnType : TypeTree = body.getType
  }
}
