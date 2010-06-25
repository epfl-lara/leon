package orderedsets

import AST.{TermVar}
import scala.collection.mutable.{HashMap => MutableMap}
import z3.scala._
import Symbol._

class Symbol private(val name: String, val tpe: Type) {
  override def toString: String = name

  private var ctx: MyZ3Context = null
  private var storedZ3Symb: Z3AST = null

  def isInt = (tpe == IntType)

  def isSet = (tpe == SetType)

  def isBool = (tpe == BoolType)

  def toZ3sym(ctxPassed: MyZ3Context): Z3AST = {
    if (ctx ne ctxPassed) {
      ctx = ctxPassed
      storedZ3Symb = ctx mkSym this
    }
    storedZ3Symb
  }

  // the collection of set variables whose inf/sup is denoted by this symbol
  var infOfList: Set[Symbol] = null
  var supOfList: Set[Symbol] = null


}

object Symbol {
  sealed abstract class Type
  case object IntType extends Type
  case object SetType extends Type
  case object BoolType extends Type

  private val counters = new MutableMap[String, Int]()
  private val interned = new MutableMap[String, Symbol]()

  private def freshName(prefix: String): String = {
    val count = counters.getOrElse(prefix, 1)
    counters.put(prefix, count + 1)
    prefix + "." + count
  }

  private def lookup(name: String, tpe: Type): Symbol = interned get name match {
    case Some(sym) =>
      if (sym.tpe != tpe) error("Incompatible types: " + sym.tpe + " and " + tpe)
      sym
    case None =>
      val sym = new Symbol(name, tpe)
      interned.put(name, sym)
      sym
  }

  def clearCache {
    counters.clear
    interned.clear
  }

  def apply(name: String, tpe: Type) = Symbol.lookup(name, tpe)

  def apply(name: String): Symbol = name.charAt(0) match {
    case c if c.isUpper => lookup(name, SetType)
    case c if c.isLower => lookup(name, IntType)
    case '?' => lookup(name, BoolType)
    case _ => error("Could not guess type of : " + name)
  }

  //  def fresh(prefix: String): Symbol =
  //    new Symbol(freshName(prefix))

  def freshInt: Symbol =
    new Symbol(freshName("t"), IntType)

  def freshSet: Symbol =
    new Symbol(freshName("S"), SetType)


  def partOf(setvar: TermVar, k: Int): Symbol =
    lookup(setvar.sym.name + "." + k, SetType)


  def equiClass(k: Int): Symbol = error("do not use")

  def equiRange(k: Int): Symbol = error("do not use")

  def partClass(setvar: TermVar, k: Int): Symbol = error("do not use")

  def partRange(setvar: TermVar, k: Int): Symbol = error("do not use")


  def infOf(setvar: TermVar): Symbol =
    lookup("inf." + setvar.sym.name, IntType)

  def supOf(setvar: TermVar): Symbol =
    lookup("sup." + setvar.sym.name, IntType)

  def beta(k: Int, setvar: TermVar): Symbol =
    lookup("pp." + k + "_" + setvar.sym.name, BoolType)

  def vennSize(k: Int, i: Int): Symbol =
    lookup("ll." + k + "." + i, IntType)

  def bool2int(sym: Symbol): Symbol =
    if (sym.isBool) new Symbol(sym.name, IntType)
    else error("Bad type : " + sym.tpe)
}
