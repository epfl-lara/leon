package orderedsets

object Example extends Unifier2[String, String] {
  val examplePage262 = List(
    'g('x2) === 'x1,
    'f('x1, 'h('x1), 'x2) === 'f('g('x3), 'x4, 'x3)
    )
  val examplePage268 = List(
    'f('x1, 'g('x2, 'x3), 'x2, 'b())
            ===
            'f('g('h('a(), 'x5), 'x2), 'x1, 'h('a(), 'x4), 'x4)
    )
  val examplePage269 = List(
    'x2 === 'h('x1, 'x1),
    'x3 === 'h('x2, 'x2),
    'x4 === 'h('x3, 'x3)
    )
  val simple1 = List('f('A) === 'g('B))
  val simple2 = List('f('A) === 'f('B, 'C))
  val simple3 = List('f('A) === 'f('f('A)))
  val simple4 = List('f('g('A), 'A) === 'f('B, 'xyz()))

  def main(args: Array[String]) {

    run(examplePage262, "Example from page 262")
    run(examplePage268, "Example from page 268")
    run(examplePage269, "Example from page 269")

    run(simple1, "Fails because the heads of the terms are different")
    run(simple2, "Fails to unify because the terms have different arity")
    run(simple3, "Infinite unification (occurs check)")
    run(simple4, "Unifies A with the atom xyz and B with the term g(xyz)")
  }

  def run(terms: List[(Term, Term)], name: String) {
    try {
      println
      println(name)
      for ((v, t) <- unify(terms))
        println("  " + v + " -> " + pp(t))
    } catch {
      case UnificationFailure(msg) =>
        println("Unification failed: " + msg)
    }
  }

  // type conversions, just for the examples

  sealed abstract class RawTerm {
    def ===(that: RawTerm): (Term, Term) = (this, that)
  }
  case class RawVar(name: String) extends RawTerm {
    def apply(terms: RawTerm*) = RawFun(name, terms.toList)
  }
  case class RawFun(name: String, args: List[RawTerm]) extends RawTerm

  implicit def str2term(sym: Symbol): RawVar = RawVar(sym.name)

  implicit def raw2term(raw: RawTerm): Term = raw match {
    case RawVar(name) => Var(name)
    case RawFun(name, args) => Fun(name, args map raw2term)
  }
}


import scala.collection.mutable.{ArrayBuffer => Seq, Map, Set, Stack}

trait Unifier2[VarName >: Null, FunName >: Null] {

  /* Interface */

  // The AST to be unified
  sealed abstract class Term
  case class Var(name: VarName) extends Term
  case class Fun(name: FunName, args: List[Term]) extends Term

  case class UnificationFailure(msg: String) extends Exception(msg)

  def pp(t: Term): String = t match {
    case Var(s) => "" + s
    case Fun(f, ts) => "" + f + (ts map pp).mkString("(", ", ", ")")
  }


  def unify(term1: Term, term2: Term): Map[VarName, Term] =
    unify(List((term1, term2)))

  def unify(terms: List[(Term, Term)]): Map[VarName, Term] = {
    val variableMap = Map[VarName, Variable]()
    def convertTerm(term: Term): Equation = term match {
      case Var(name) => variableMap get name match {
        case Some(v) =>
          new Equation(v)
        case None =>
          val v = Variable(name)
          variableMap(name) = v
          new Equation(v)
      }
      case Fun(name, args) =>
        new Equation(Function(name, Seq(args: _*) map convertTerm))
    }
    val frontier = terms map {x => merge(convertTerm(x._1), convertTerm(x._2))}
    val dummyVariable = new Variable(null)
    dummyVariable.eqclass.eqn.fun = Some(new Function(null, Seq(frontier: _*)))

    val allVariables = Seq(dummyVariable) ++ variableMap.values
    unify(allVariables map {_.eqclass}) - null
  }

  /* Implementation */

  private case class Variable(name: VarName) {
    // The equivalence class for that variable
    var eqclass: Equivalence = new Equivalence(this)

    override def toString = "" + name
  }
  private case class Function(val name: FunName, val eqns: Seq[Equation]) {
    override def toString = name + eqns.mkString("(", ",", ")")
  }
  private class Equation(val vars: Set[Variable] = Set(),
                         var fun: Option[Function] = None) {
    def this(v: Variable) = this (vars = Set(v))

    def this(f: Function) = this (fun = Some(f))

    override def toString = {
      if (fun.isEmpty) vars.mkString("{", ",", "}")
      else if (vars.isEmpty) fun.mkString
      else vars.mkString("{", ",", "}") + " = " + fun.mkString
    }
  }
  private class Equivalence(val eqn: Equation) {
    def this(v: Variable) = this (new Equation(v))

    // How often variables in this class occur on the right-hand side
    // of other terms
    var refCounter = 0

    override def toString = "[" + refCounter + "] " + eqn
  }

  private def unify(equivalences: Seq[Equivalence]): Map[VarName, Term] = {
    var numberOfClasses = equivalences.size
    val substitutions = Map[VarName, Term]()
    val freeClasses = Stack[Equivalence]() // Equations with a zero ref counter

    // Initialize reference counters
    def countRefs(fun: Function) {
      for (eqn <- fun.eqns) {
        for (v <- eqn.vars) v.eqclass.refCounter += 1
        for (f <- eqn.fun) countRefs(f)
      }
    }
    for (equiv <- equivalences; f <- equiv.eqn.fun) countRefs(f)
    for (equiv <- equivalences; if equiv.refCounter == 0) freeClasses push equiv

    def compact(cl1: Equivalence, cl2: Equivalence) = {
      if (cl1 == cl2) cl1
      else {
        numberOfClasses -= 1
        merge(cl1, cl2)
      }
    }

    // Main loop
    while (numberOfClasses > 0) {
      // Select multi equation
      if (freeClasses.isEmpty) throw UnificationFailure("cycle")

      val currentClass = freeClasses.pop
      val currentVars = currentClass.eqn.vars
      currentClass.eqn.fun match {
        case Some(function) =>
          val (commonPart, frontier) = reduce(function)

          for (v <- currentVars)
            substitutions(v.name) = commonPart

          // Compact equations (i.e. merge equivalence classes)
          for (eqn <- frontier) {
            val eqclass = (eqn.vars map {_.eqclass}) reduceLeft compact
            eqclass.refCounter -= eqn.vars.size
            merge(eqclass.eqn, eqn)
            if (eqclass.refCounter == 0) freeClasses push eqclass
          }
        case None =>
          val representative = Var(currentVars.head.name)
          for (v <- currentVars.tail) substitutions(v.name) = representative
      }
      numberOfClasses -= 1
    }
    substitutions
  }

  private def merge(class1: Equivalence, class2: Equivalence): Equivalence = {
    if (class1 == class2) return class1 // should not happen !?
    if (class1.eqn.vars.size < class2.eqn.vars.size)
      return merge(class2, class1)

    merge(class1.eqn, class2.eqn)
    class1.refCounter += class2.refCounter
    for (v <- class2.eqn.vars)
      v.eqclass = class1
    class1
  }

  private def merge(equation1: Equation, equation2: Equation): Equation = {
    if (equation1 == equation2) return equation1 // should not happen !?

    equation1.vars ++= equation2.vars
    equation1.fun match {
      case None => equation1.fun = equation2.fun
      case Some(Function(name1, args1)) => equation2.fun match {
        case Some(Function(name2, args2)) =>
          if (name1 != name2) throw UnificationFailure("clash")
          if (args1.size != args2.size) throw UnificationFailure("arity")
          val args = for ((eqn1, eqn2) <- args1 zip args2) yield merge(eqn1, eqn2)
          equation1.fun = Some(Function(name1, args))
        case None =>
      }
    }
    equation1
  }

  private def reduce(function: Function) = {
    val frontier = Seq[Equation]()
    def rec(function1: Function): Term = {
      val args = for (arg <- function1.eqns) yield {
        if (arg.vars.isEmpty) {
          rec(arg.fun.get)
        } else {
          frontier += arg
          Var(arg.vars.head.name)
        }
      }
      Fun(function1.name, args.toList)
    }
    (rec(function), frontier)
  }

}