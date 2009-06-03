package funcheck.purescala

import Common._

/** AST definitions for Pure Scala. */
object Trees {
  sealed abstract class Expr

  /** Types of Pure Scala.
   Go through each type, add the operations.
     map update
     concatenation of lists
     random access on lists
     set union, intersection, etc.

   Lambda abstraction and application of function values

   Separately, function calls

   equality on sets, ADTs etc. (equality on function types?!)

   forall, exists - optionally bounded quantifiers
     * comes with type A of bound variable 
     * also comes with an optional Set[A] that gives more precise description of the range of this variable

    Without Set[A] bound, the variable ranges over all constructible (not only allocated) objects.

see examples in:
     http://code.google.com/p/scalacheck/wiki/UserGuide
   */
  case class IfExpr(cond : Expr, then : Expr, elze : Expr) extends Expr

  //case class MatchCase(constructor : CaseClassType,
  //		       boundVars : Seq[MatchCase]) // not really

  //case class MatchExpr(scrutinee : Expr, cases : Seq[MatchCase]) extends Expr
  
  case class IntLiteral(value: Int) extends Expr
  case class BooleanLiteral(value: Boolean) extends Expr
  case class Equals(left: Expr, right: Expr) extends Expr

  /** Types of Pure Scala. */

  // support for:
  //  - Any
  //  - integers
  //  - Lists
  //  - n-uples
  //  - ADTs
  //  - classes 
  //  - sets
  //  - maps
  //  - function type constructor for lambda expr.

  //  - maybe strings some day?

  sealed abstract class TypeTree

  case object AnyType extends TypeTree
  case object BooleanType extends TypeTree
  case object Int32Type extends TypeTree

  case class ListType(base: TypeTree) extends TypeTree
  case class TupleType(bases: Seq[TypeTree]) extends TypeTree { lazy val dimension: Int = bases.length }
  case class FunctionType(arg: TypeTree, res: TypeTree) extends TypeTree
  case class SetType(base: TypeTree) extends TypeTree
  case class MapType(from: TypeTree, to: TypeTree) extends TypeTree
  case class ClassType(id: Identifier) extends TypeTree
  case class CaseClassType(id: Identifier) extends TypeTree

  // Definitions

  type VarDecl = (Identifier,TypeTree)
  type VarDecls = Seq[VarDecl]

  sealed abstract class Definition(name : Identifier)
  case class CaseClassDef(name : Identifier, fields : VarDecls) extends Definition(name)
  case class ClassDef(name : Identifier, fields : VarDecls) extends Definition(name)
  case class ValDef(name : Identifier, value : Expr) extends Definition(name)
  case class FunDef(name : Identifier, params : VarDecls, body : Expr) extends Definition(name) {
    var returnType : TypeTree = _
  }
  case class ObjectDef(name : Identifier, defs : Seq[Definition]) extends Definition(name)
}
