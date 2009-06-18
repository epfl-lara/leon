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

  // The object and class members have to be known at construction time. The
  // typed members can be added anytime.
  class ObjectSymbol(
    val id: Identifier,
    val classes: Seq[ClassSymbol],
    val objects: Seq[ObjectSymbol]) extends Symbol {

    private var _fields: List[VariableSymbol] = Nil
    private var _functions: List[FunctionSymbol] = Nil

    def fields: Seq[VariableSymbol] = _fields
    def  functions: Seq[FunctionSymbol] = _functions

    def registerField(f: VariableSymbol): ObjectSymbol = {
      _fields = _fields ::: List(f)
      this
    }

    def registerFunction(f: FunctionSymbol): ObjectSymbol = {
      _functions = _functions ::: List(f)
      this
    }

    override def toString: String = withInc(0)

    private def withInc(inc: Int): String = {
      val ii: String = "    " * inc
      ii + "[object: " + id + "\n" +
      (if(!fields.isEmpty) {
        ii + " fields: " + fields.map(_.toString).mkString("{ ", ", ", " }") + "\n"
      } else { "" }) +
      (if(!functions.isEmpty) {
        ii + " functions: " + functions.map(_.toString).mkString("{ ", ", ", " }") + "\n"
      } else { "" }) +
      (if(!classes.isEmpty) {
        ii + " classes: " + classes.map(_.toString).mkString("{ ", ", ", " }") + "\n" 
      } else { "" }) +
      (if(!objects.isEmpty) {
        ii + " objects: " + objects.map(_.withInc(inc+1)).mkString("{\n", ",\n", "\n" + ii + " }") + "\n"
      } else { "" }) +
      ii + "]"
    }
  }

  sealed abstract class ClassSymbol extends Symbol {
    val parents: Seq[AbstractClassSymbol]

    protected val _pfx: String

    override def toString = "[" + _pfx + ": " + id + (if (!parents.isEmpty) { " extends " + parents.mkString(", ") } else { "" }) + "]"
  }

  /** Symbols for abstract classes (or traits) */
  class AbstractClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol {
    override protected val _pfx = "abstract class"
  }

  /** Symbols for "regular" (= non-abstract, non-case) classes */
  class RefClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol {
    override protected val _pfx = "class"
  }

  /** Symbols for case classes. */
  class CaseClassSymbol(val id: Identifier, val parents: Seq[AbstractClassSymbol]) extends ClassSymbol {
    override protected val _pfx = "case class"
  }

  class FunctionSymbol(val id: Identifier, val params: Seq[VariableSymbol], val returnType: TypeTree) extends Typed {
    def getType = returnType
  }
}
