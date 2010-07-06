package orderedsets

import scala.collection.immutable.Queue
import purescala.Reporter
import purescala.Extensions.Solver
import Reconstruction.Model
import purescala.Trees._
import purescala.Common._
import purescala.Definitions._

// TODO: Extend Reporter
object Unifier {
  case class UnifierException(str: String) extends Exception(str)

   /* This function replaces the subexpression in tree with the variable,
   * Hence, the name Reverse Map.
   */
  private def transformRevMap(revMap: Queue[(Variable, Expr)])(t: Expr): Expr =
    if(revMap.isEmpty) t
    else transformRevMap(revMap.tail)(transform(revMap.head._2, revMap.head._1)(t))

  /* For performing one substitution on the tree.
   */
  private def transform(v: Expr, substVal: Expr)(t: Expr): Expr = t match {
    case v1 if v1 == v => substVal
    case CaseClassSelector(t1, selector) => CaseClassSelector(transform(v, substVal)(t1), selector)
    case CaseClass(cc, args) => CaseClass(cc, args map transform(v, substVal))
    case Equals(t1, t2) => Equals( transform(v, substVal)(t1), transform(v, substVal)(t2) )
    case Not(e @ Equals(_, _)) => Not( transform(v, substVal)(e) )
    case And(lst) => And(lst map transform(v, substVal))
    case _ => t
  }
  
  /* Makes the equality constraints from equal CaseClass arguments
  */
  private def makeConstr(arg1: Seq[Expr], arg2: Seq[Expr]): List[Equals] = {
    arg1.zip(arg2).map(x => Equals(x._1,x._2)).toList
  }

  /* Occurs check
   */
  private def notOccurs(v : Variable)(tr: Expr): Boolean = tr match {
    case v2 @ Variable(_) if v2 == v => false
    case Variable(_) => true
    case CaseClassSelector(t1, _) => notOccurs(v)(t1)
    case CaseClass(_, args) => (true /: args) {_ && notOccurs(v)(_)}
    case _ => throw(new UnifierException("Cannot handle expression : " + tr))
  }

  /* Unification on a list of expressions
   * The CaseClassSelector is assumed to be replaced with fresh variabled throughout.
  */
  private def unify(constr: List[Expr]) : Map[Variable, Expr] =
    if(constr.isEmpty) Map.empty
    else constr.head match {
      case Equals(Variable(id1), Variable(id2)) if id1 == id2 => unify(constr.tail)
      case Equals(t1, t2) if t1 == t2 => unify(constr.tail)
      case Equals(v @ Variable(id1), tr) if notOccurs(v)(tr) => unifyBaseCase(v, tr, constr.tail)
      case Equals(tr, v @ Variable(id1)) if notOccurs(v)(tr) => unifyBaseCase(v, tr, constr.tail)
      case Equals(a @ CaseClass(cc1, args1), b @ CaseClass(cc2, args2)) if (cc1 == cc2) => unify( makeConstr(args1, args2) ++ constr.tail)
      case Equals(a, b) => throw(new UnifierException("Cannot unify " + a + " and " + b ))
      case _ => throw(new UnifierException("Illegal expression in unifier: " + constr.head))
    }

  
  /* Unification on the base case.
  */
  private def unifyBaseCase(v: Variable, t1: Expr, rest: Seq[Expr]) = {
    val subst = transform(v, t1) _
    val substitutedTail = rest.map( {case Equals(t1, t2) => Equals(subst(t1), subst(t2)); case t => throw(new UnifierException("Cannot handle expression: " + t)) } ).toList
    unify(substitutedTail).updated(v, t1)
  }

  /* Resursively substitute the variables to come at the most concrete expression as possible
   */
  private def recSubst(varMap: Map[Variable, Expr], tr: Expr): Expr = tr match {
    case v @ Variable(_) if varMap.contains(v) => recSubst(varMap, varMap(v))
    case Variable(_) => tr
    case CaseClassSelector(tr, fld) => CaseClassSelector(recSubst(varMap, tr), fld)
    case CaseClass(cc, args) => CaseClass(cc, args map (x => recSubst(varMap, x)))
    case _ => throw(new UnifierException("Unifier cannot handle: " + tr))
  }

  /* To check whether this substitution preserves the Inequality constraints
   */
  private def isInEqSatisfied(varMap: Map[Variable, Expr], inEq: Seq[Expr]): Boolean = if(inEq.isEmpty) true
    else inEq.head match {
      case Not(Equals(t1, t2)) if (recSubst(varMap, t1) == recSubst(varMap, t2)) => false
      case _ => isInEqSatisfied(varMap, inEq.tail)
    }

  /* Replaces CaseClassSelector with fresh variables in a given expression
   */
  private def replaceCCSinExpr(t1: Expr): (Expr, Queue[(Variable, Expr)]) = t1 match {
    case Variable(_) => (t1, Queue.empty)
    case ccs @ CaseClassSelector(t1, id) =>
      val (subExpr, inMap) = replaceCCSinExpr(t1)
      val freshVar = Variable(FreshIdentifier("UnifVal", true)).setType(ccs.getType)
      // The new variables added in the reverse order
      (freshVar, inMap.enqueue(freshVar, CaseClassSelector(subExpr, id)))
    case CaseClass( cc, args ) => {
      val (subArgs, revMap) = replaceCCSinSeq(args)
      (CaseClass(cc, subArgs), revMap)
    }
    case t => throw(new UnifierException("Unifier cannot handle expression = " + t))
  }
      
  /* Replaces CaseClassSelector with fresh variabled in a given sequence of expressions
   */
  private def replaceCCSinSeq(eqConstr: Seq[Expr]): (Seq[Expr], Queue[(Variable, Expr)]) =
    if(eqConstr.isEmpty) (Seq.empty, Queue.empty)
    else eqConstr.head match {
      case Not(Equals(t1, t2)) => 
        val (sub1::sub2::Nil, revMap) = replaceCCSinSeq(List(t1,  t2))
        val newTail = eqConstr.tail map (transformRevMap(revMap))
        val (newSeq, newMap) = replaceCCSinSeq( newTail )
        ((Not(Equals(sub1, sub2)) :: newSeq.toList), newMap ++ revMap)
      case Equals(t1, t2) =>
        val (sub1::sub2::Nil, revMap) = replaceCCSinSeq(List(t1,  t2))
        val newTail = eqConstr.tail map (transformRevMap(revMap))
        val (newSeq, newMap) = replaceCCSinSeq( newTail )
        ((Equals(sub1, sub2) :: newSeq.toList), newMap ++ revMap)
      case t1 => 
        val (sub, revMap) = replaceCCSinExpr(t1)
        val newTail = eqConstr.tail map (transformRevMap(revMap))
        val (newSeq, newMap) = replaceCCSinSeq( newTail )
        ((sub :: newSeq.toList), newMap ++ revMap)
    }

  /* The public function which can be called to get the implications of performing
   * unification. Either returns a conjunction of equalities, or else, an exception
   */
  def unify(form : And) : And = {
    
    // Extract constraints
    val And(constraints) = form

    // Replace CaseClassSelector expressions with fresh variables
    val (cleanConstr, revMapQueue) = replaceCCSinSeq( constraints )
    val revMap = Map.empty ++ revMapQueue
    // println("\nReverse map:")
    // revMap.foreach( println(_) )

    // Get equality constraints
    val equalConstr = cleanConstr.filter( {case Equals(_,_) => true; case _ => false} )
    // println(equalConstr)

    // Get ineqality constraints
    val notEqualConstr =  cleanConstr.filter( {case Not(Equals(_,_)) => true; case _ => false} )

    // The mapping (including the fresh variables) which are the result of unification
    val varMap = unify(equalConstr.toList)
    // println("\nActual map:")
    // varMap.foreach( println(_) )

    // Check if the inequalities are satisfied
    if(isInEqSatisfied(varMap, notEqualConstr)) 

        // Recursively replace the fresh variables introduced
        And(varMap.map( x => Equals(recSubst(revMap, x._1), recSubst(revMap, x._2)) ).toList)
    else throw(new UnifierException("Inequality constraints cannot be satisfied."))
  }

  def main(args: Array[String]) = {
    val CC1 = new CaseClassDef(FreshIdentifier("Node"))
    val a = Variable(FreshIdentifier("a"))
    val b = Variable(FreshIdentifier("b"))
    val c = Variable(FreshIdentifier("c"))
    val x = Variable(FreshIdentifier("x"))
    val CC1_inst = CaseClass(CC1, List(a))
    val CC2_inst = CaseClass(CC1, List(x))


    val eq1 = Equals(CC1_inst, b)
    val eq2 = Equals(CaseClass(CC1, List(c)), b)
    var form =  And( List(eq1, eq2) ) 
    var res = unify(form)
    println("Formula = " + form)
    println("Result = " + res)
    println()

    // Fails occurs check
    val eq3 = Equals(CC1_inst, c)
    try {
      form =  And( List(eq1, eq2, eq3) ) 
      println("Formula = " + form)
      res = unify(form)
      println("Result = " + res)
      println()
    } catch {
      case e => println("Exception: " + e + "\n")
    }

    // Fails InEqCheck
    val eq4 = Not(Equals(a, c))
    try {
      form =  And( List(eq1, eq2, eq4) ) 
      println("Formula = " + form)
      res = unify(form)
      println("Result = " + res)
      println()
    } catch {
      case e => println("Exception: " + e + "\n")
    }

    // Uses Unification over CaseClassSelector, probably incorrectly
    val Variable(id_a) = a
    val Variable(id_x) = x
    val d = Variable(FreshIdentifier("d"))
    val e = Variable(FreshIdentifier("e"))
    val Sel1 = CaseClassSelector( CC1_inst, id_a )
    val Sel2 = CaseClassSelector( CC1_inst, id_a )
    
    val revQueue = Queue.empty.enqueue(a -> Sel1).enqueue(b -> e)
    println("Trying substitution:")
    println(transformRevMap(revQueue)(And(List(Equals(Sel2,b), Not(Equals(Sel1,e))))))
    println()

    val eq5 = Equals(Sel1, d)
    val eq6 = Equals(Sel2, e)
    try {
      form =  And( List(eq1, eq2, eq5, eq6) ) 
      println("Formula = " + form)
      res = unify(form)
      println("Result = " + res)
      println()
    } catch {
      case e => println("Exception: " + e + "\n")
    }
  }

}

