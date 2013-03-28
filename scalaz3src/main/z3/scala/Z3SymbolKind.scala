package z3.scala

sealed abstract class Z3SymbolKind[T] {
  val value: T
}

case class Z3IntSymbol private[z3](value: Int) extends Z3SymbolKind[Int]
case class Z3StringSymbol private[z3](value: String) extends Z3SymbolKind[String]
