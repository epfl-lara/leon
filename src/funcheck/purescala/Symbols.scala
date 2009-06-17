package funcheck.purescala

import Common._
import TypeTrees._

/** There's a need for symbols, as we have purely functional trees with
 * potential recursive calls, and we want references to be resolved once and
 * for all. */
object Symbols {
  trait Symbolic {
    self =>

    private var __s: Option[Symbol] = None

    def symbol: Symbol = __s.getOrElse(throw new Exception("Undefined symbol."))

    def setSymbol(s: Symbol): self.type = __s match {
      case Some(_) => throw new Exception("Symbol already set.")
      case None => { __s = Some(s); this }
    }
  }

  sealed abstract class Symbol {
    val id: Identifier
  }
  
  class VariableSymbol(val id: Identifier, val tpe: TypeTree) extends Typed {
    def getType = tpe
  }

  class ObjectSymbol(
    val id: Identifier,
    val fields: Seq[VariableSymbol],
    val functions: Seq[FunctionSymbol],
    val classes: Seq[ClassSymbol],
    val objects: Seq[ObjectSymbol]) extends Symbol

  sealed abstract class ClassSymbol {
    val parents: Seq[AbstractClassSymbol]
  }

  /** Symbols for abstract classes (or traits) */
  class AbstractClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol

  /** Symbols for "regular" (= non-abstract, non-case) classes */
  class RefClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol

  /** Symbols for case classes. */
  class CaseClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol

  class FunctionSymbol(val id: Identifier, val params: Seq[VariableSymbol], val returnType: TypeTree) extends Typed {
    def getType = returnType
  }
}
