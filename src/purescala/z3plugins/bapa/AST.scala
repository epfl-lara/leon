package purescala.z3plugins.bapa

import z3.scala._

object AST {
  
  /* AST */

  case class IllegalTerm(tree: Tree) extends Exception(tree + " should not be present in the formula.")


  sealed abstract class Tree {
    override def toString = PrettyPrinter(this)
    def ||(tree: Tree) = Op(OR, Seq(this, tree))
    def &&(tree: Tree) = Op(AND, Seq(this, tree))
    def unary_! = Op(NOT, Seq(this))
    def iff(tree: Tree) = Op(IFF, Seq(this, tree))
    def ===(tree: Tree) = Op(EQ, Seq(this, tree))
    def =!=(tree: Tree) = !(this === tree)
    def <(tree: Tree) = Op(LT, Seq(this, tree))
    def <=(tree: Tree) = !(tree < this)
    def >(tree: Tree) = tree < this
    def >=(tree: Tree) = !(this < tree)
    def seteq(tree: Tree) = Op(SETEQ, Seq(this, tree))
    def subseteq(tree: Tree) = Op(SUBSETEQ, Seq(this, tree))
    def +(tree: Tree) = Op(ADD, Seq(this, tree))
    def ifThenElse(then: Tree, elze: Tree) = Op(ITE, Seq(this, then, elze))
    def card = Op(CARD, Seq(this))
    def ++(tree: Tree) = Op(UNION, Seq(this, tree))
    def **(tree: Tree) = Op(INTER, Seq(this, tree))
    def --(tree: Tree) = this ** ~tree
    def unary_~ = Op(COMPL, Seq(this))
  }
  case class Op(op: Operand, args: Seq[Tree]) extends Tree
  case class Lit(lit: Literal) extends Tree
  case class Var(sym: Symbol) extends Tree
 
  /* AST extractors */

  // Seems to be broken (scala bug ?)
  /*
  object UnOp {
    def unapply(tree: Tree): Option[(Operand, Tree)] = tree match {
      case Op(op, Seq(t)) => Some(op, t)
      case _ => None
    }
  }

  object BinOp {
    def unapply(tree: Tree): Option[(Operand, Tree, Tree)] = tree match {
      case Op(op, Seq(t1, t2)) => Some(op, t1, t2)
      case _ => None
    }
  }

  object TernOp {
    def unapply(tree: Tree): Option[(Operand, Tree, Tree, Tree)] = tree match {
      case Op(op, Seq(t1, t2, t3)) => Some(op, t1, t2, t3)
      case _ => None
    }
  }
  */

  /* Literals */

  sealed abstract class Literal
  case object TrueLit extends Literal
  case object FalseLit extends Literal
  case class IntLit(value: Int) extends Literal
  case object EmptySetLit extends Literal
  case object FullSetLit extends Literal

  val True = Lit(TrueLit)
  val False = Lit(FalseLit)
//   val Zero = Lit(IntLit(0))
//   val One = Lit(IntLit(1))
  val EmptySet = Lit(EmptySetLit)
  val FullSet = Lit(FullSetLit)

  implicit def int2tree(i: Int) = Lit(IntLit(i))

  /* Operands */
 
  sealed abstract class Operand(val name: String) {
    override def toString = name
  }
  // return booleans
  case object OR extends Operand("||")
  case object AND extends Operand("&&")
  case object NOT extends Operand("!")
  case object IFF extends Operand("<=>")
  case object EQ extends Operand("==")
  case object LT extends Operand("<")
  case object LESS extends Operand("<<") // less-than for min / max
  case object SETEQ extends Operand("seteq")
  case object SUBSETEQ extends Operand("subseteq")
  // return integers
  case object ADD extends Operand("+")
  case object ITE extends Operand("IF-THEN-ELSE")
  case object CARD extends Operand("CARD")
  case object CARD_PRED extends Operand("CARD-predicate")
  case object MIN extends Operand("MIN")
  case object MAX extends Operand("MAX")
  // return sets
  case object UNION extends Operand("++")
  case object INTER extends Operand("**")
  case object COMPL extends Operand("~")

  /* Types */

  sealed abstract class Type
  case object BoolType extends Type
  case object IntType extends Type
  case object SetType extends Type

  /* Symbols */

  class Symbol private[AST](val typ: Type, val ast: Z3AST) {
    def name = ast.toString
    override def toString = name
    override def hashCode = ast.ptr.hashCode
    override def equals(that: Any) =
      ( that != null &&
        that.isInstanceOf[Symbol] &&
        that.asInstanceOf[Symbol].ast.ptr == this.ast.ptr )
  }


//   object Symbol {
    /*
    def apply(typ: Type, z3: Z3Context, ast: Z3AST): Symbol = z3.getASTKind(ast) match {
      case Z3AppAST(decl, Nil) =>
//         val name = z3sym2string(z3, z3.getDeclName(decl))
        new Symbol(typ, z3.getDeclName(decl).toString, ast)
      case Z3AppAST(decl, Seq(set)) =>
        //val name = "Z3_TH_" + z3.getDeclName(decl) + "(" + set + ")"
        new Symbol(typ, decl(set).toString, ast)
      case bad => error("Z3AST is not a variable : " + bad)
    }
    */
//     def apply(typ: Type, z3: Z3Context, ast: Z3AST): Symbol =
//       new Symbol(typ, ast)
    /*
    def unapply(sym: Symbol): Option[(Type,Z3AST)] =
      Some(sym.typ, sym.ast)
    */
//   }

//   private def z3sym2string(z3: Z3Context, sym: Z3Symbol): String = z3.getSymbolKind(sym) match {
//     case Z3IntSymbol(i) => i.toString
//     case Z3StringSymbol(s) => s
//   }

  implicit def sym2tree(sym: Symbol): Tree = Var(sym)

  def BoolSymbol(ast: Z3AST) = new Symbol(BoolType, ast)
  def IntSymbol(ast: Z3AST) = new Symbol(IntType, ast)
  def SetSymbol(ast: Z3AST) = new Symbol(SetType, ast)

}
