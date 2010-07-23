package setconstraints

import setconstraints.Trees._

object PrettyPrinter {

  def apply(f: Formula): String = ppFormula(f)

  def apply(st: SetType): String = ppSetType(st)

  private def ppFormula(f: Formula): String = f match {
    case And(fs) => fs.map(ppFormula).mkString("(", " \u2227 ", ")")
    case Include(s1, s2) => ppSetType(s1) + " \u2282 " + ppSetType(s2)
  }

  private def ppSetType(st: SetType): String = st match {
    case ConstructorType(name, Seq()) => name
    case ConstructorType(name, sts) => name + sts.map(ppSetType).mkString("(", ", ", ")")
    case UnionType(sts) => sts.map(ppSetType).mkString("(", " \u222A ", ")")
    case IntersectionType(sts) => sts.map(ppSetType).mkString("(", " \u2229 ", ")")
    case FunctionType(s1, s2) => "(" + ppSetType(s1) + " --> " + ppSetType(s2) + ")"
    case TupleType(sts) => sts.map(ppSetType).mkString("(", ", ", ")")
    case VariableType(name) => name
  }
}
