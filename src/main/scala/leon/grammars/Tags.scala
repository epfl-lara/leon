/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Types.CaseClassType
import purescala.Definitions.FunDef

object Tags {
  /** A class for tags that tag a [[ProductionRule]] with the kind of expression in generates. */
  abstract class Tag
  case object Top       extends Tag // Tag for the top-level of the grammar (default)
  case object Zero      extends Tag // Tag for 0
  case object One       extends Tag // Tag for 1
  case object BooleanC  extends Tag // Tag for boolean constants
  case object Constant  extends Tag // Tag for other constants
  case object And       extends Tag // Tags for boolean operations
  case object Or        extends Tag
  case object Not       extends Tag
  case object Plus      extends Tag // Tags for arithmetic operations
  case object Minus     extends Tag
  case object Times     extends Tag
  case object Mod       extends Tag
  case object Div       extends Tag
  case object Variable  extends Tag // Tag for variables
  case object Equals    extends Tag // Tag for equality
  /** Constructors like Tuple, CaseClass... 
    * 
    * @param isTerminal If true, this constructor represents a terminal symbol
    *                  (in practice, case class with 0 fields)
    */
  case class Constructor(isTerminal: Boolean) extends Tag
  /** Tag for function calls
    *
    * @param isMethod Whether the function called is a method
    * @param isSafe Whether this constructor represents a safe function call.
    *               We need this because this call implicitly contains a variable,
    *               so we want to allow constants in all arguments.
    */
  case class FunCall(isMethod: Boolean, isSafe: Boolean) extends Tag

  /** The set of tags that represent constants */
  val isConst: Set[Tag] = Set(Zero, One, Constant, BooleanC, Constructor(true))

  /** The set of tags that represent commutative operations */
  val isCommut: Set[Tag] = Set(Plus, Times, Equals)

  /** The set of tags which have trivial results for equal arguments */
  val symmetricTrivial = Set(Minus, And, Or, Equals, Div, Mod)

  /** Tags which allow constants in all their operands
    *
    * In reality, the current version never allows that: it is only allowed in safe function calls
    * which by construction contain a hidden reference to a variable.
    * TODO: Experiment with different conditions, e.g. are constants allowed in
    * top-level/ general function calls/ constructors/...?
    */
  def allConstArgsAllowed(t: Tag) = t match {
    case FunCall(_, true) => true
    case _ => false
  }

  def tagOf(cct: CaseClassType) = Constructor(cct.fields.isEmpty)
  def tagOf(fd: FunDef, isSafe: Boolean) = FunCall(fd.methodOwner.isDefined, isSafe)
}