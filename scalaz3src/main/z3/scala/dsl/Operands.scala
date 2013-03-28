package z3.scala.dsl

/** We call Operands what is otherwise known as "Rich" classes (from the "Pimp
 * My Library" paradigm). For simplicity and to avoid ambiguous resolutions,
 * operations on operands always return operands, never trees. Conversion from
 * and to trees are done by implicit functions in the dsl package object. */
object Operands {
  class BoolOperand private[dsl](val tree : Tree[_ >: BottomSort <: BoolSort]) {
    def &&[T >: BottomSort <: BoolSort](other : BoolOperand) : BoolOperand = {
      new BoolOperand(And(tree, other.tree))
    }

    def ||(other : BoolOperand) : BoolOperand = {
      new BoolOperand(Or(tree, other.tree))
    }
    
    def unary_! : BoolOperand= {
      new BoolOperand(Not(tree))
    }

    def <-->(other : BoolOperand) : BoolOperand = {
      new BoolOperand(Iff(tree, other.tree))
    }

    def ===(other : BoolOperand) = <-->(other)

    def -->(other : BoolOperand) : BoolOperand = {
      new BoolOperand(Implies(tree, other.tree))
    }

    def ^^(other : BoolOperand) : BoolOperand = {
      new BoolOperand(Xor(tree, other.tree))
    }

    def !==(other : BoolOperand) = ^^(other)
  }

  class IntOperand private[dsl](val tree : Tree[_ >: BottomSort <: IntSort]) {
    def +(other : IntOperand) : IntOperand= {
      new IntOperand(Add(tree, other.tree))
    }

    def *(other : IntOperand) : IntOperand = {
      new IntOperand(Mul(tree, other.tree))
    }

    def -(other : IntOperand) : IntOperand = {
      new IntOperand(Sub(tree, other.tree))
    }

    def /(other : IntOperand) : IntOperand = {
      new IntOperand(Div(tree, other.tree))
    }

    def %(other : IntOperand) : IntOperand = {
      new IntOperand(Mod(tree, other.tree))
    }

    def rem(other : IntOperand) : IntOperand = {
      new IntOperand(Rem(tree, other.tree))
    }

    def ===(other : IntOperand) : BoolOperand = {
      new BoolOperand(Eq(tree, other.tree))
    }

    def !==(other : IntOperand) : BoolOperand = {
      new BoolOperand(Distinct(tree, other.tree))
    }

    def <(other : IntOperand) : BoolOperand = {
      new BoolOperand(LT(tree, other.tree))
    }

    def <=(other : IntOperand) : BoolOperand = {
      new BoolOperand(LE(tree, other.tree))
    }

    def >(other : IntOperand) : BoolOperand = {
      new BoolOperand(GT(tree, other.tree))
    }

    def >=(other : IntOperand) : BoolOperand = {
      new BoolOperand(GE(tree, other.tree))
    }
  }

  class SetOperand private[dsl](val tree : Tree[_ >: BottomSort <: SetSort]) {
    def ++(other : SetOperand) : SetOperand = {
      new SetOperand(SetUnion(tree, other.tree))
    }

    def **(other : SetOperand) : SetOperand = {
      new SetOperand(SetIntersect(tree, other.tree))
    }

    def --(other : SetOperand) : SetOperand = {
      new SetOperand(SetDifference(tree, other.tree))
    }

    def ===(other : SetOperand) : BoolOperand = {
      new BoolOperand(Eq(tree, other.tree))
    }

    def !==(other : SetOperand) : BoolOperand = {
      new BoolOperand(Distinct(tree, other.tree))
    }

    def subsetOf(other : SetOperand) : BoolOperand = {
      new BoolOperand(SetSubset(tree, other.tree))
    }
  }
}
