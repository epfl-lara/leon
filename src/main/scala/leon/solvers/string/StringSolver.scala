package leon.solvers.string

import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.solvers.Solver
import leon.utils.Interruptible
import leon.LeonContext
import scala.collection.mutable.ListBuffer
import vanuatoo.Pattern
import scala.annotation.tailrec

/**
 * @author Mikael
 */
object StringSolver {
  type Assignment = Map[Identifier, String]
  
  type StringFormToken = Either[String, Identifier]
  
  type StringForm = List[StringFormToken]
  
  type Equation = (StringForm, String)
  
  /** Sequences of equalities such as xyz"1"uv"2" = "1, 2" */
  type Problem = List[Equation]
  
  /** Evaluates a String form. Requires the solution to have an assignment to all identifiers. */
  @tailrec def evaluate(s: Assignment, acc: StringBuffer = new StringBuffer(""))(sf: StringForm): String = sf match {
    case Nil => acc.toString
    case Left(constant)::q => evaluate(s, acc append constant)(q)
    case Right(identifier)::q => evaluate(s, acc append s(identifier))(q)
  }
  
  /** Assigns the new values to the equations and simplify them at the same time. */
  @tailrec def reduceStringForm(s: Assignment, acc: ListBuffer[StringFormToken] = ListBuffer())(sf: StringForm): StringForm = sf match {
    case Nil => acc.toList
    case (l@Left(constant))::(l2@Left(constant2))::q => reduceStringForm(s, acc)(Left(constant + constant2)::q)
    case (l@Left(constant))::(r2@Right(id))::q =>
      s.get(id) match {
        case Some(sid) =>
          reduceStringForm(s, acc)(Left(constant + sid)::q)
        case None =>
          reduceStringForm(s, (acc += l) += r2)(q)
      }
    case (l@Left(constant))::q => reduceStringForm(s, acc += l)(q)
    case (r@Right(id))::q =>
      s.get(id) match {
        case Some(sid) =>
          reduceStringForm(s, acc)(Left(sid)::q)
        case None =>
          reduceStringForm(s, acc += r)(q)
      }
  }
  
  /** Assignes the variable to their values in all equations and simplifies them. */
  def reduceProblem(s: Assignment, acc: ListBuffer[Equation] = ListBuffer())(p: Problem): Problem = p match {
    case Nil => acc.toList
    case ((sf, rhs)::q) => reduceProblem(s, acc += ((reduceStringForm(s)(sf): StringForm, rhs)))(q)
  }
  
  /** Returns true if the assignment is a solution to the problem */
  def check(p: Problem, s: Assignment): Boolean = {
    p forall (eq => evaluate(s)(eq._1) == eq._2 )
  }
  
  /** Concatenates constants together */
  def reduceStringForm(s: StringForm): StringForm =  {
    @tailrec def rec(s: StringForm, acc: ListBuffer[StringFormToken] = ListBuffer()): StringForm = s match {
      case Nil => acc.toList
      case Left(c)::Left(d)::q => rec(Left(c+d)::q, acc)
      case a::q => rec(q, acc += a)
    }
    rec(s)
  }
  
  /** returns a simplified version of the problem. If it is not satisfiable, returns None. */
  @tailrec def simplifyProblem(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
    // Invariant: Every assigned var does not appear in the problem.
    // 1. Merge constant in string forms
    @tailrec def mergeConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
      case Nil => Some(acc.toList)
      case (sf, rhs)::q => mergeConstants(q, acc += ((reduceStringForm(sf), rhs)))
    }
    
    // 2. Unsat if Const1 = Const2 but constants are different.
    // 2bis.    if Const1 = Const2 and constants are same, remove equality.
    @tailrec def simplifyConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
      case Nil => Some(acc.toList)
      case (Nil, rhs)::q => if("" != rhs) None else simplifyConstants(q, acc)
      case (List(Left(c)), rhs)::q => if(c != rhs) None else simplifyConstants(q, acc)
      case sentence::q => simplifyConstants(q, acc += sentence)
    }
    
    // 3. Get new assignments from equations such as id = Const.
    @tailrec def obtainAssignments(p: Problem, assignments: Assignment = Map()): Option[Assignment] = p match {
      case Nil => Some(assignments)
      case (List(Right(id)), rhs)::q =>
        assignments.get(id) match { // It was assigned already.
          case Some(v) =>
            if(rhs != v) None else obtainAssignments(q, assignments)
          case None => 
            obtainAssignments(q, assignments + (id -> rhs))
        }
      case sentence::q => obtainAssignments(q, assignments)
    }
    val simplifiedOpt = mergeConstants(p)
    .flatMap(simplifyConstants(_))
    
    simplifiedOpt match {
      case None => None
      case Some(simplified) =>
        // 4. If there are new assignments, forward them to the equation and relaunch the simplification.
        val newAssignmentsOpt = obtainAssignments(simplified)
        newAssignmentsOpt match {
          case Some(newAssignments) if newAssignments.nonEmpty =>
             simplifyProblem(reduceProblem(newAssignments)(simplified), s ++ newAssignments)
          case _ => Some((simplified, s))
        }
    }
  }
  
  object ConsReverse {
    def unapply[A](l: List[A]): Option[(List[A], A)] = {
      if(l.nonEmpty) Some((l.init, l.last)) else None
    }
    def apply[A](q: List[A], a: A): List[A] = q :+ a
  }
  
  // Removes all constants from the left and right of the equations
  def noLeftRightConstants(p: Problem): Option[Problem] = {
    @tailrec def removeLeftconstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
      case Nil => Some(acc.toList)
      case ((Left(constant)::q, rhs))::ps =>
        if(rhs.startsWith(constant)) {
          removeLeftconstants(ps, acc += ((q, rhs.substring(constant.length))))
        } else None
      case (t@(q, rhs))::ps =>
        removeLeftconstants(ps, acc += t)
    }
    
    @tailrec def removeRightConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
      case Nil => Some(acc.toList)
      case (ConsReverse(q, Left(constant)), rhs)::ps =>
        if(rhs.endsWith(constant)) {
          removeRightConstants(ps, acc += ((q, rhs.substring(0, rhs.length - constant.length))))
        } else None
      case (t@(q, rhs))::ps =>
        removeRightConstants(ps, acc += t)
    }
    
    removeLeftconstants(p).flatMap(removeRightConstants(_))
  }
  
  /** Composition of simplifyProble and noLeftRightConstants */
  def forwardStrategy(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
    leon.utils.fixpoint[Option[(Problem, Assignment)]]{
        case None => None
        case Some((p: Problem, assignment: Assignment)) =>
          val simplified = simplifyProblem(p, Map())
          if(simplified == None) None else {
            val simplified_problem = simplified.get._1
            val simplified2_problem = noLeftRightConstants(simplified_problem)
            if(simplified2_problem == None) None else {
              Some((simplified2_problem.get, assignment ++ simplified.get._2))
            }
          }
    }(Option((p, s)))
  }
  
  /** Returns all start positions of the string s in text.*/
  def occurrences(s: String, text: String): List[Int] = {
    ("(?="+java.util.regex.Pattern.quote(s)+")").r.findAllMatchIn(text).map(m => m.start).toList
  }
  
  /** Returns a list of all possible positions of the constants inside the string */
  def repartitions(constants: List[String], text: String): List[List[Int]] = constants match {
    case Nil => List(List())
    case c::q => 
      occurrences(c, text).flatMap(startPos =>
        repartitions(q, text.substring(startPos + c.length))
        .map(startPos :: _.map(_ + (startPos + c.length))))
  }
  
  /** Computes the Combinatorial coefficient c(n, k)*/
  def cnk(n: BigInt, k: BigInt): BigInt = {
    var res = BigInt(1)
    var i = 0
    while(i < k) {
      res *= n - i
      i+=1
    }
    i = 2
    while(i <= k) {
      res /= i
      i+=1
    }
    res
  }
  
  /** Solves the equation   x1x2x3...xn = CONSTANT */
  def simpleSplit(ids: List[Identifier], rhs: String): Stream[Assignment] = {
    ids match {
    case Nil => if(rhs == "") Stream(Map()) else Stream.empty
    case List(x) => 
      Stream(Map(x -> rhs))
    case x :: ys => for{
      i <- (0 to rhs.length).toStream
      xvalue = rhs.substring(0, i)
      rvalue = rhs.substring(i)
      remaining_splits = simpleSplit(ys, rvalue)
      remaining_split <- remaining_splits
      if !remaining_split.contains(x) || remaining_split(x) == xvalue
    } yield (remaining_split + (x -> xvalue))
  }
  }
  
  /** Deduces possible new assignments from the problem. */
  def splitStrategy(p: Problem): Stream[Assignment] = {
    // Look for the equation with the least degree of freedom.
    if(p.isEmpty) return Stream(Map())
    
    var minStatement = p.head
    var minweight = BigInt(-1)
    var minConstants = List[String]()
    var minIdentifiersGrouped = List[List[Identifier]]()
    // Counts the number of possible enumerations, take the least.
    for((lhs, rhs) <- p) {
      val constants = lhs.collect{ case Left(constant) => constant }
      val identifiers_grouped = ListBuffer[List[Identifier]]()
      var current_buffer = ListBuffer[Identifier]()
      for(e <- lhs) e match {
        case Left(constant) => // At this point, there is only one constant here.
          identifiers_grouped.append(current_buffer.toList)
          current_buffer.clear()
        case Right(identifier) =>
          current_buffer.append(identifier)
      }
      identifiers_grouped.append(current_buffer.toList)
      var weight = BigInt(9)
      for(positions <- repartitions(constants, rhs)) {
        var tmp_weight = BigInt(1) 
        var prev_position = 0
        for(((p, c), ids) <- positions.zip(constants).zip(identifiers_grouped.init)) {
          tmp_weight *= cnk(p - prev_position, ids.length - 1) // number of positions
          prev_position = p + c.length
        }
        tmp_weight *= cnk(rhs.length - prev_position, identifiers_grouped.last.length - 1)
        weight += tmp_weight
      }
      if(minweight == -1 || weight < minweight) {
        minweight = weight
        minStatement = (lhs, rhs)
        minConstants = constants
        minIdentifiersGrouped = identifiers_grouped.toList
      }
    }
    val (lhs, rhs) = minStatement
    val constants = minConstants
    val identifiers_grouped = minIdentifiersGrouped
    if(identifiers_grouped.length > 1) {
      // There might be different repartitions of the first boundary constant. We need to investigate all of them.
      repartitions(constants, rhs).map(_.head).distinct.toStream.flatMap(p => {
        val firstString = rhs.substring(0, p)
        simpleSplit(identifiers_grouped.head, firstString)
      })
    } else if(identifiers_grouped.length == 1) {
      simpleSplit(identifiers_grouped.head, rhs) // All new assignments
    } else {
      if(rhs == "") Stream(Map()) else Stream.Empty
    }
  }
  
  /** Solves the problem and returns all possible satisfying assignment */
  def solve(p: Problem): Stream[Assignment] = {
    val realProblem = forwardStrategy(p, Map())
    
    realProblem match {
      case None => Stream.Empty
      case Some((Nil, solution)) =>
        Stream(solution)
      case Some((problem, partialSolution)) =>
        // 1) No double constants ("a" + "b" have been replaced by "ab")
        // 2) No just an identifier on the LHS (x = "a" has been replaced by an assignment
        // 3) No leading or trailing constants in equation ("a" + ... + "b"  = "axyzb" has been replaced by ... = "xyz")
        
        /* Equation of the type
           variables "constant" variables "constant".... variables = "constant".
           For each constant we check its possible positions in the output, which determines possible assignments.
           
           Then since variables = constant, we can just iterate on them.
           Heuristic: We need to resolve smaller equations first.
        */
        for{assignment <- splitStrategy(problem)
            newProblem = reduceProblem(assignment)(problem)
            remainingSolution <- solve(newProblem)
         } yield {
          partialSolution ++ assignment ++ remainingSolution
        }
    }
  }
  
  ////////////////////////////////////////////////
  //// Transitively Bounded problem extension ////
  ////////////////////////////////////////////////
  
  /** More general types of equations */
  type GeneralEquation = (StringForm, StringForm)
  
  /** Supposes that all variables are transitively bounded by length*/
  type GeneralProblem = List[GeneralEquation]
  
  def variablesStringForm(sf: StringForm): Set[Identifier] = (sf.collect{ case Right(id) => id }).toSet
  def variables(gf: GeneralEquation): Set[Identifier] = variablesStringForm(gf._1) ++ variablesStringForm(gf._2)
  
  /** Returns true if the problem is transitively bounded */
  def isTransitivelyBounded(b: GeneralProblem, transitivelyBounded: Set[Identifier] = Set()): Boolean = {
    def isBounded(sf: GeneralEquation) = {
      variablesStringForm(sf._1).forall(transitivelyBounded) || variablesStringForm(sf._2).forall(transitivelyBounded)
    }
    val (bounded, notbounded) = b.partition(isBounded _)
    
    if(notbounded == Nil) true
    else if(notbounded == b) false
    else {
      isTransitivelyBounded(notbounded, transitivelyBounded ++ bounded.flatMap { x => variables(x) })
    }
  }

  /** Propagates an assignment into a general equation */
  def reduceGeneralEquation(a: Assignment)(g: GeneralEquation): GeneralEquation = g match {
    case (sf1, sf2) => (reduceStringForm(a)(sf1), reduceStringForm(a)(sf2))
  }
  
  /** Solves the bounded problem version.
    * Requires all the variables to be transitively bounded by size. */
  def solveGeneralProblem(b: GeneralProblem): Stream[Assignment] = {
    val realProblem = b map { case (lhs, rhs) => (reduceStringForm(lhs), reduceStringForm(rhs)) }
    
    def partition(b: GeneralProblem, bounded: ListBuffer[Equation] = ListBuffer(), unbounded: ListBuffer[GeneralEquation] = ListBuffer()): (Problem, GeneralProblem) = b match {
      case Nil => (bounded.toList, unbounded.toList)
      case (sf1, List(Left(a)))::q => partition(q, bounded += ((sf1, a)), unbounded)
      case (sf1, Nil)::q => partition(q, bounded += ((sf1, "")), unbounded)
      case (List(Left(a)), sf1)::q => partition(q, bounded += ((sf1, a)), unbounded)
      case (Nil, sf1)::q => partition(q, bounded += ((sf1, "")), unbounded)
      case a::q => partition(q, bounded, unbounded += a)
    }
    
    val (bounded, unbounded) = partition(realProblem)
    
    if(unbounded == Nil) solve(bounded) else
    solve(bounded).flatMap(assignment => {
      solveGeneralProblem(unbounded.map(reduceGeneralEquation(assignment)(_))).map(assignment ++ _)
    })
  }
}