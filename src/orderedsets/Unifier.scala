package orderedsets

import scala.{Symbol => ScalaSymbol}

object ExampleUnifier extends Unifier[String, String] {

  // Tests and Examples
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
      case UnificationImpossible(msg) =>
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

  implicit def str2term(sym: ScalaSymbol): RawVar = RawVar(sym.name)

  implicit def raw2term(raw: RawTerm): Term = raw match {
    case RawVar(name) => Var(name)
    case RawFun(name, args) => Fun(name, args map raw2term)
  }


  def pv(str: String) = str

  def pf(str: String) = str
}

import scala.collection.mutable.ArrayBuffer
import scala.collection.Map
import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions.CaseClassDef


object ADTUnifier extends Unifier[Variable, CaseClassDef] {
  def pv(v: Variable) = v.id.toString

  def pf(cc: CaseClassDef) = cc.id.toString

  def freshVar(prefix: String)(typed: Typed) = Var(Variable(FreshIdentifier(prefix, true) setType typed.getType))

  def unify(conjunction: Seq[Expr]): (Seq[Expr], Map[Variable, Expr]) = {
    val equalities = new ArrayBuffer[(Term, Term)]()
    val inequalities = new ArrayBuffer[(Var, Var)]()

    def extractEquality(expr: Expr): Unit = expr match {
      case Equals(t1, t2) =>
        equalities += expr2term(t1) -> expr2term(t2)
      case Not(Equals(t1, t2)) =>
        inequalities += toPureTerm(t1) -> toPureTerm(t2)
      case _ => error("Should not happen after separating the formula.")
    }
    def toPureTerm(expr: Expr) = expr2term(expr) match {
      case v@Var(_) => v
      case term =>
        val v = freshVar("Diseq")(expr)
        equalities += v -> term
        v
    }
    def expr2term(expr: Expr): Term = expr match {
      case v@Variable(id) => Var(v)
      case CaseClass(ccdef, args) => Fun(ccdef, args map expr2term)
      case CaseClassSelector(ex, sel) =>
        val CaseClassType(ccdef) = ex.getType
        val args = ccdef.fields map freshVar("Sel")
        equalities += expr2term(ex) -> Fun(ccdef, args)
        args(ccdef.fields findIndexOf {_.id == sel})
      case _ => error("Should not happen after separating the formula.")
    }
    // extract equality constraints
    conjunction foreach extractEquality

    /*
    println
    println("--- Input to the unifier ---")
    for ((l,r) <- equalities) println("  " + pp(l) + "  =  " + pp(r))
    if (!inequalities.isEmpty) {
      println("and")
      for ((l,r) <- inequalities) println("  " + pp(l) + "  !=  " + pp(r))
    }    
    println
    // */

    val mgu = unify(equalities.toList)
    val table = blowUp(mgu)
    def subst(v: Variable) = table getOrElse (v, Var(v))

    /*
    def byName(entry1: (Variable,Term), entry2: (Variable,Term)) =
      pv(entry1._1) < pv(entry2._1)
    
    //println
    println("--- Output of the unifier (MGU) ---")
    for ((x, t) <- mgu.toList sortWith byName)
      println("  " + x + "  =  " + pp(t))
    println
  
    val substTable = table mapValues term2expr
    println("--- Output of the unifier (Substitution table) ---")
    for ((x, t) <- substTable.toList sortWith {_._1.id.name < _._1.id.name})
      println("  " + x + "  =  " + t)
    // */


    // check inequalities
    for ((Var(x1), Var(x2)) <- inequalities) {
      val t1 = subst(x1)
      val t2 = subst(x2)
      if (t1 == t2)
        throw UnificationImpossible("'" + x1.id + " != " + x2.id + "' violated") // (both reduce to " + pp(t1) + ")")
    }

    /*
    if (!inequalities.isEmpty)
      println("Inequalities were checked to hold\n")
    
    println("--- Output of the unifier (Substitution table) ---")
    val map1 = map.filterKeys{_.getType != NoType}
    for ((x, t) <- map1.toList sortWith byName)
      println("  " + x + "  =  " + pp(t))
    if (map1.isEmpty) println("  (empty table)")
    println 
    */

    // Extract element equalities and disequalities
    val elementFormula = new ArrayBuffer[Expr]()
    for ((e1, term) <- table; if isElementType(e1)) {
      term2expr(term) match {
        case e2@Variable(_) =>
          //println("  " + e1 + ": " + e1.getType +
          //    "  ->  " + e2 + ": " + e2.getType) 
          elementFormula += Equals(e1, e2)
        case expr =>
          //println("  " + e1 + ": " + e1.getType +
          //    "  ->  " + expr + ": " + expr.getType)
          //println("UNEXPECTED: " + term)
          error("Unexpected " + expr)
      }
    }
    for ((Var(e1), Var(e2)) <- inequalities; if isElementType(e1))
      elementFormula += Not(Equals(e1, e2))

    (elementFormula.toSeq, table mapValues term2expr)
  }

  def term2expr(term: Term): Expr = term match {
    case Var(v) => v
    case Fun(cd, args) => CaseClass(cd, args map term2expr)
  }

  def isElementType(typed: Typed) = typed.getType match {
    case AbstractClassType(_) | CaseClassType(_) => false
    case _ => true
  }

}



import scala.collection.mutable.{ArrayBuffer => Seq, Map => MutableMap, Set, Stack}

case class UnificationImpossible(msg: String) extends Exception(msg)

trait Unifier[VarName >: Null, FunName >: Null] {
  type MGU = Seq[(VarName, Term)]
  type Subst = MutableMap[VarName, Term]

  // transitive closure for the mapping - the smart way (in only one iteration)
  def blowUp(mgu: MGU): Subst = {
    val map = MutableMap[VarName, Term]()
    def subst(term: Term): Term = term match {
      case Var(v) => map get v match {
        case Some(t) => t
        case None => term
      }
      case Fun(f, args) => Fun(f, args map subst)
    }
    for ((v, t) <- mgu.reverse) {
      map(v) = subst(t)
    }
    map
  }

  /* Interface */

  // The AST to be unified
  sealed abstract class Term
  case class Var(name: VarName) extends Term
  case class Fun(name: FunName, args: scala.collection.Seq[Term]) extends Term




  def pv(s: VarName): String

  def pf(f: FunName): String

  def _pv(s: VarName): String = if (s == null) "<null>" else pv(s)

  def _pf(f: FunName): String = if (f == null) "<null>" else pf(f)

  def pp(t: Term): String = t match {
    case Var(s) => _pv(s)
    case Fun(f, ts) => _pf(f) + (ts map pp).mkString("(", ", ", ")")
  }


  def unify(term1: Term, term2: Term): MGU =
    unify(List((term1, term2)))

  def unify(terms: List[(Term, Term)]): MGU = {
    val variableMap = MutableMap[VarName, Variable]()
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
    unify(allVariables map {_.eqclass}) filter {_._1 != null}
  }

  /* Data structures */

  private case class Variable(name: VarName) {
    // The equivalence class for that variable
    var eqclass: Equivalence = new Equivalence(this)

    override def toString = _pv(name)
  }
  private case class Function(val name: FunName, val eqns: Seq[Equation]) {
    override def toString = _pf(name) + eqns.mkString("(", ",", ")")
  }
  private class Equation(val vars: Seq[Variable] = Seq(),
                         var fun: Option[Function] = None) {
    def this(v: Variable) = this (vars = Seq(v))

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

  /* Implementation */

  private def unify(equivalences: Seq[Equivalence]): MGU = {
    var numberOfClasses = equivalences.size
    val substitutions = Seq[(VarName, Term)]()
    val freeClasses = Stack[Equivalence]() // Equations with a zero ref counter

    /*
    val vars = equivalences map {_.eqn.vars.head}
    val fvars = Seq[Variable]()
    */

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
      /*
      println()
      println("U:")
      println("  vars : " + vars.mkString(", "))
        val classes = (vars map {_.eqclass}).toSet
        println(classes.size + " / " + numberOfClasses)
        for (cl <- classes) println(cl)
      println("T: ")
      println("  vars : " + fvars.mkString(", "))
        for ((v,t) <- substitutions) println("  " + v + " -> " + pp(t))
      */

      // Select multi equation
      if (freeClasses.isEmpty) throw UnificationImpossible("cycle")

      val currentClass = freeClasses.pop
      val currentVars = currentClass.eqn.vars
      val representative = Var(currentVars.head.name)
      for (v <- currentVars.tail)
        substitutions += (v.name -> representative)

      currentClass.eqn.fun match {
        case Some(function) =>
          val (commonPart, frontier) = reduce(function)
          substitutions += (representative.name -> commonPart)

          // Compact equations (i.e. merge equivalence classes)
          for (eqn <- frontier) {
            /*
            println(eqn)
            */
            val eqclass = (eqn.vars map {_.eqclass}) reduceLeft compact
            eqclass.refCounter -= eqn.vars.size
            eqn.vars.clear
            merge(eqclass.eqn, eqn)
            if (eqclass.refCounter == 0) freeClasses push eqclass

            /*
            println("  " + eqclass)
            */
          }
        case None =>
      }
      numberOfClasses -= 1

      /*
      vars --= currentVars
      fvars ++= currentVars
      */
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
          if (name1 != name2) throw UnificationImpossible("clash")
          if (args1.size != args2.size) throw UnificationImpossible("arity")
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