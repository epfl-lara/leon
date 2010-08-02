package setconstraints

import setconstraints.Trees._

object PrettyPrinter {

  def apply(f: Formula): String = ppFormula(f)

  def apply(st: SetType): String = ppSetType(st)

  def apply(fp: FixPoint): String = ppFixPoint(fp)

  private def ppFormula(f: Formula): String = f match {
    case And(fs) => fs.map(ppFormula).mkString("(  ", "\n \u2227 ", ")")
    case Include(s1, s2) => ppSetType(s1) + " \u2286 " + ppSetType(s2)
    case Equals(s1, s2) => ppSetType(s1) + " = " + ppSetType(s2)
  }

  private def ppSetType(st: SetType): String = st match {
    case ConstructorType(name, Seq()) => name
    case ConstructorType(name, sts) => name + sts.map(ppSetType).mkString("(", ", ", ")")
    case UnionType(sts) => sts.map(ppSetType).mkString("(", " \u222A ", ")")
    case IntersectionType(sts) => sts.map(ppSetType).mkString("(", " \u2229 ", ")")
    case ComplementType(s) => "\u00AC" + ppSetType(s)
    case FunctionType(s1, s2) => "(" + ppSetType(s1) + " --> " + ppSetType(s2) + ")"
    case TupleType(sts) => sts.map(ppSetType).mkString("(", ", ", ")")
    case VariableType(name) => name
    case EmptyType => "0"
    case UniversalType => "1"
  }

  private def ppFixPoint(fp: FixPoint): String = fp match {
    case FixPoint(t, s) => ppSetType(t) + " = " + ppSetType(s)
  }
}
