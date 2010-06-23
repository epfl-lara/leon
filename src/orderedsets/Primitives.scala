package orderedsets


object Primitives {
  sealed abstract class Literal
  case class IntLit(value: Int) extends Literal
  case object EmptySetLit extends Literal
  case object FullSetLit extends Literal
  //case object InfinityLit extends Literal


  sealed abstract class Primitive(val name: String) {
    override def toString: String = name

    def isLogical: Boolean

    def isIntOp: Boolean
  }


  trait Logical extends Primitive {def isLogical = true}
  trait NonLogical extends Primitive {def isLogical = false}
  trait IntOperand extends Primitive {def isIntOp = true}
  trait SetOperand extends Primitive {def isIntOp = false}

  // logical primitives on integers
  case object LT extends Primitive("<") with Logical with IntOperand
  case object LE extends Primitive("<=") with Logical with IntOperand
  case object EQ extends Primitive("=") with Logical with IntOperand
  case object NE extends Primitive("!=") with Logical with IntOperand
  case object GT extends Primitive(">") with Logical with IntOperand
  case object GE extends Primitive(">=") with Logical with IntOperand

  // non-logical primitives on integers
  // TODO: do we need DIV and MOD ?
  case object ADD extends Primitive("+") with NonLogical with IntOperand
  case object SUB extends Primitive("-") with NonLogical with IntOperand
  case object MUL extends Primitive("*") with NonLogical with IntOperand
  case object SINGLETON extends Primitive("SINGLETON") with NonLogical with SetOperand
  case class ITE(f: AST.Formula) extends Primitive("if-then-else") with NonLogical with IntOperand
  //  case object DIV extends Primitive("/") with NonLogical with IntOperand
  //  case object MOD extends Primitive("%") with NonLogical with IntOperand
  case object MIN extends Primitive("min") with NonLogical with IntOperand
  case object MAX extends Primitive("max") with NonLogical with IntOperand

  // logical primitives on sets
  case object SEQ extends Primitive("==") with Logical with SetOperand
  case object SLT extends Primitive("<<") with Logical with SetOperand
  case object SELEM extends Primitive("in") with Logical with SetOperand
  case object SUBSETEQ extends Primitive("c=") with Logical with SetOperand

  // non-logical primitives on sets
  // - SetOperands return sets, IntOperands return ints
  case object UNION extends Primitive("++") with NonLogical with SetOperand
  case object INTER extends Primitive("**") with NonLogical with SetOperand
  //case object MINUS extends Primitive("--") with NonLogical with SetOperand
  case object COMPL extends Primitive("COMPL") with NonLogical with SetOperand
  case object LRANGE extends Primitive("LRANGE") with NonLogical with SetOperand
  case object TAKE extends Primitive("TAKE") with NonLogical with SetOperand
  case object CARD extends Primitive("CARD") with NonLogical with IntOperand
  case object INF extends Primitive("INF") with NonLogical with IntOperand
  case object SUP extends Primitive("SUP") with NonLogical with IntOperand

  type IntLogical = Logical with IntOperand
  val negate: IntLogical => IntLogical =
  Map(List(LT, LE, EQ, NE, GT, GE) zip List(GE, GT, NE, EQ, LE, LT): _*)
}
  
