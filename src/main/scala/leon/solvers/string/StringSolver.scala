/* Copyright 2009-2016 EPFL, Lausanne */

package leon.solvers.string

import leon.purescala.Common._
import scala.collection.mutable.ListBuffer
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
  
  def renderStringForm(sf: StringForm): String = sf match {
    case Left(const)::Nil => "\""+const+"\"" 
    case Right(id)::Nil => id.toString
    case Left(const)::q =>  "\""+const+"\"+" + renderStringForm(q)
    case Right(id)::q => id.toString + "+" + renderStringForm(q)
    case Nil => ""
  }
  
  def renderProblem(p: Problem): String = {
    def renderEquation(e: Equation): String = {
      renderStringForm(e._1) + "==\""+e._2+"\""
    }
    p match {case Nil => ""
    case e::q => renderEquation(e) + ", " + renderProblem(q)}
  }
  
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
  
  /** Computes a foldable property on the problem */
  def fold[T](init: T, s: StringFormToken => T, f: (T, T) => T)(p: Problem) = {
    p.view.foldLeft(init) {
      case (t, (lhs, rhs)) =>
        lhs.view.foldLeft(t) {
          case (t, sft) => f(t, s(sft))
        }
    }
  }
  
  /** Returns true if there is a StringFormToken which satisfies the given property */
  def exists(s: StringFormToken => Boolean)(p: Problem) = fold[Boolean](false, s, _ || _)(p)
  /** Counts the number of StringFormToken which satisfy the given property */
  def count(s: StringFormToken => Boolean)(p: Problem) = fold[Int](0, s andThen (if(_) 1 else 0), _ + _)(p)
  
  /** Maps every StringFormToken of the problem to create a new one */
  def map(s: StringFormToken => StringFormToken)(p: Problem): Problem = {
    p.map { case (lhs, rhs) => (lhs map s, rhs) }
  }
  
  /** Returns true if the assignment is a solution to the problem */
  def errorcheck(p: Problem, s: Assignment): Option[String] = {
    val res = p flatMap {eq =>
      val resultNotCorrect = reduceStringForm(s)(eq._1) match {
        case Left(a)::Nil if a == eq._2 => None
        case Nil if eq._2 == "" => None
        case res => Some(res)
      }
      if(resultNotCorrect.nonEmpty) Some(renderStringForm(eq._1) + " == "+ renderStringForm(resultNotCorrect.get) + ", but expected " + eq._2) else None
    }
    if(res == Nil) None else Some(res.mkString("\n") + "\nAssignment: " + s)
  }
  
  /** Concatenates constants together */
  def reduceStringForm(s: StringForm): StringForm =  {
    @tailrec def rec(s: StringForm, acc: ListBuffer[StringFormToken] = ListBuffer()): StringForm = s match {
      case Nil => acc.toList
      case Left("")::q => rec(q, acc)
      case Left(c)::Left(d)::q => rec(Left(c+d)::q, acc)
      case a::q => rec(q, acc += a)
    }
    rec(s)
  }
  
  /** Split the stringFrom at the last constant.
    * @param s The concatenation of constants and variables  
    * @return (a, b, c) such that a ++ Seq(b) ++ c == s and b is the last constant of s */
  def splitAtLastConstant(s: StringForm): (StringForm, StringFormToken, StringForm) = {
    val i = s.lastIndexWhere(x => x.isInstanceOf[Left[_, _]])
    (s.take(i), s(i), s.drop(i+1))
  }
  
  /** Use `val ConsReverse(init, last) = list` to retrieve the n-1 elements and the last element directly. */
  object ConsReverse {
    def unapply[A](l: List[A]): Option[(List[A], A)] = {
      if(l.nonEmpty) Some((l.init, l.last)) else None
    }
    def apply[A](q: List[A], a: A): List[A] = q :+ a
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
  
  def prioritizedPositions(s: String): Stream[Int] = {
    val separations = "\\b".r.findAllMatchIn(s).map(m => m.start).toList
    separations.toStream #::: {
      val done = separations.toSet
      for( i <- (0 to s.length).toStream if !done(i)) yield i
    }
  }
  
  
  /** A single pass simplification process. Converts as much as equations to assignments if possible. */
  trait ProblemSimplicationPhase { self =>
    def apply(p: Problem, s: Assignment) = run(p, s)
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)]
    def andThen(other: ProblemSimplicationPhase): ProblemSimplicationPhase = new ProblemSimplicationPhase {
      def run(p: Problem, s: Assignment) = {
        ProblemSimplicationPhase.this.run(p, s) match {
          case Some((p, s)) => 
            //println("Problem before " + other.getClass.getName.substring(33) + ":" + (renderProblem(p), s))
            other.run(p, s)
          case None =>
            None
        }
      }
    }
    /** Applies a phase until the output does not change anymore */
    def loopUntilConvergence = new ProblemSimplicationPhase {
      def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
        leon.utils.fixpoint[Option[(Problem, Assignment)]]{
          case None => None
          case Some((problem: Problem, assignment: Assignment)) => self.run(problem, assignment)
        }(Option((p, s)))
      }
    }
  }
  def loopUntilConvergence(psp: ProblemSimplicationPhase) = psp.loopUntilConvergence 
  
  /** Removes duplicate equations from the problem */
  object DistinctEquation extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      Some((p.distinct, s))
    }
  }
  
  /** Merge constant in string forms */
  object MergeConstants extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      @tailrec def mergeConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
        case Nil => Some(acc.toList)
        case (sf, rhs)::q => mergeConstants(q, acc += ((reduceStringForm(sf), rhs)))
      }
      mergeConstants(p).map((_, s))
    }
  }
  
  /** Unsat if Const1 = Const2 but constants are different.
    * if Const1 = Const2 and constants are same, remove equality. */
  object SimplifyConstants extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      @tailrec def simplifyConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
        case Nil => Some(acc.toList)
        case (Nil, rhs)::q => if("" != rhs) None else simplifyConstants(q, acc)
        case (List(Left(c)), rhs)::q => if(c != rhs) None else simplifyConstants(q, acc)
        case sentence::q => simplifyConstants(q, acc += sentence)
      }
      simplifyConstants(p).map((_, s))
    }
  }
  
  /** . Get new assignments from equations such as id = Const, and propagate them */
  object PropagateAssignments extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
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
      obtainAssignments(p, s).map(newAssignments => {
        //println("Obtained new assignments: " + newAssignments)
        val newProblem = if(newAssignments.nonEmpty) reduceProblem(newAssignments)(p) else p
        (newProblem, s ++ newAssignments)
      })
    }
  }

  /** Removes all constants from the left of the equations (i.e. "ab" x ... = "abcd" ==> x ... = "cd" ) */
  object RemoveLeftConstants extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      @tailrec def removeLeftconstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
        case Nil => Some(acc.toList)
        case ((Left(constant)::q, rhs))::ps =>
          if(rhs.startsWith(constant)) {
            removeLeftconstants(ps, acc += ((q, rhs.substring(constant.length))))
          } else None
        case (t@(q, rhs))::ps =>
          removeLeftconstants(ps, acc += t)
      }
      removeLeftconstants(p).map((_, s))
    }
  }
  
  /** Removes all constants from the right of the equations (i.e. ... x "cd" = "abcd" ==> ... x = "ab" ) */
  object RemoveRightConstants extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      @tailrec def removeRightConstants(p: Problem, acc: ListBuffer[Equation] = ListBuffer()): Option[Problem] = p match {
        case Nil => Some(acc.toList)
        case (ConsReverse(q, Left(constant)), rhs)::ps =>
          if(rhs.endsWith(constant)) {
            removeRightConstants(ps, acc += ((q, rhs.substring(0, rhs.length - constant.length))))
          } else None
        case (t@(q, rhs))::ps =>
          removeRightConstants(ps, acc += t)
      }
      removeRightConstants(p).map((_, s))
    }
  }
   
  /** If constants can have only one position in an equation, splits the equation.
    * If an equation is empty, treats all left-hand-side identifiers as empty.
    * Requires MergeConstants so that empty constants have been removed. */
  object PropagateMiddleConstants extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      @tailrec def constantPropagate(p: Problem, assignments: Assignment = Map(), newProblem: ListBuffer[Equation] = ListBuffer()): Option[(Problem, Assignment)] = {
        p match {
          case Nil => 
            Some((newProblem.toList, assignments))
          case (ids, "")::q => // All identifiers should be empty.
            val constants = ids.find { 
              case Left(s) if s != "" => true
              case Right(_) => false
            }
            (constants match {
              case Some(_) => None
              case None => // Ok now let's assign all variables to empty string.
                val newMap = ids.collect { case Right(id) => id -> "" }
                val newAssignments = (Option(assignments) /: newMap) {
                  case (None, (id, rhs)) => None 
                  case (Some(a), (id, rhs)) => 
                    a.get(id) match { // It was assigned already.
                      case Some(v) =>
                        if(rhs != v) None else Some(a)
                      case None => 
                        Some(a + (id -> rhs))
                    }
                }
                newAssignments
            }) match {
              case None => None
              case Some(a) => 
                constantPropagate(q, a, newProblem)
            }
          case (sentence@(ids, rhs))::q => // If the constants have an unique position, we should split the equation.
            val constants = ids.collect { 
              case l@Left(s) => s
            }
            // Check if constants form a partition in the string, i.e. getting the .indexOf() the first time is the only way to split the string.
            
            if(constants.nonEmpty) {
              
              var pos = -2
              var lastPos = -2
              var lastConst = ""
              var invalid = false
              
              for(c <- constants) {
                val i = rhs.indexOfSlice(c, pos)
                lastPos = i
                lastConst = c
                if(i == -1) invalid = true
                pos = i + c.length
              }
              if(invalid) None else {
                val i = rhs.indexOfSlice(lastConst, lastPos + 1)
                if(i == -1) { // OK it's the smallest position possible, hence we can split at the last position.
                  val (before, _, after) = splitAtLastConstant(ids)
                  val firstConst = rhs.substring(0, lastPos)
                  val secondConst = rhs.substring(lastPos + lastConst.length)
                  constantPropagate((before, firstConst)::(after, secondConst)::q, assignments, newProblem)
                } else {
                  // Other splitting strategy: independent constants ?
                  
                  val constantsSplit = constants.flatMap{ c => {
                    val i = rhs.indexOfSlice(c, -1)
                    val j = rhs.indexOfSlice(c, i + 1)
                    if(j == -1 && i != -1) {
                      List((c, i))
                    } else Nil
                  }}
                  
                  constantsSplit match {
                    case Nil =>
                     constantPropagate(q, assignments, newProblem += sentence)
                    case ((c, i)::_) =>
                      val (before, after) = ids.splitAt(ids.indexOf(Left(c)))
                      val firstconst = rhs.substring(0, i)
                      val secondConst = rhs.substring(i+c.length)
                      constantPropagate((before, firstconst)::(after.tail, secondConst)::q, assignments, newProblem)
                  }
                  
                }
              }
            } else {
              constantPropagate(q, assignments, newProblem += sentence)
            }
          case sentence::q => constantPropagate(q, assignments, newProblem += sentence)
        }
      }
      constantPropagate(p).map(ps => {
        val newP = if(ps._2.nonEmpty) reduceProblem(ps._2)(p) else p
        (newP, s ++ ps._2)
      })
    }
  }
  
  /** If a left-hand side of the equation appears somewhere else, replace it by the right-hand-side of this equation */
  object PropagateEquations extends ProblemSimplicationPhase {
    def run(p: Problem, s: Assignment): Option[(Problem, Assignment)] = {
      var newP = p.distinct
      for((lhs, rhs) <- newP if lhs.length >= 2) { // Original distinct p.
        var indexInP = 0
        for(eq@(lhs2, rhs2) <- newP)  {
          if((!(lhs2 eq lhs) || !(rhs2 eq rhs))) {
            val i = lhs2.indexOfSlice(lhs)
            if(i != -1) {
              val res = (lhs2.take(i) ++ Seq(Left(rhs)) ++ lhs2.drop(i + lhs.size), rhs2)
              newP = newP.updated(indexInP, res)
            }
          }
          indexInP += 1
        }
      }
      Some((newP, s))
    }
  }
  
  /** returns a simplified version of the problem. If it is not satisfiable, returns None. */
  val simplifyProblem: ProblemSimplicationPhase = {
    loopUntilConvergence(DistinctEquation andThen
    MergeConstants andThen
    SimplifyConstants andThen
    PropagateAssignments)
  }
  
  /** Removes all constants from the left and right of the equations */
  val noLeftRightConstants: ProblemSimplicationPhase = {
    RemoveLeftConstants andThen RemoveRightConstants
  }
  
  /** Composition of simplifyProblem and noLeftRightConstants */
  val forwardStrategy =
    loopUntilConvergence(simplifyProblem andThen noLeftRightConstants andThen PropagateMiddleConstants andThen PropagateEquations)
  
  
  /** Solves the equation   x1x2x3...xn = CONSTANT
    * Prioritizes split positions in the CONSTANT that are word boundaries
    * Prioritizes variables which have a higher frequency */
  def simpleSplit(ids: List[Identifier], rhs: String)(implicit statistics: Map[Identifier, Int]): Stream[Assignment] = {
    ids match {
      case Nil => if(rhs == "") Stream(Map()) else Stream.empty
      case List(x) => 
        Stream(Map(x -> rhs))
      case x :: ys => 
        val (bestVar, bestScore, worstScore) = ((None: Option[(Identifier, Int, Int)]) /: ids) {
          case (None, x) => val sx = statistics(x)
            Some((x, sx, sx))
          case (s@Some((x, i, ws)), y) => val yi = statistics(y)
            if (i >= yi) Some((x, i, Math.min(yi, ws))) else Some((y, yi, ws))
        }.get
        val pos = prioritizedPositions(rhs)
        val numBestVars = ids.count { x => x == bestVar }

        if(worstScore == bestScore) {
          for{
            i <- pos // Prioritization on positions which are separators.
            xvalue = rhs.substring(0, i)
            rvalue = rhs.substring(i)
            remaining_splits = simpleSplit(ys, rvalue)
            remaining_split <- remaining_splits
            if !remaining_split.contains(x) || remaining_split(x) == xvalue
          } yield (remaining_split + (x -> xvalue))
        } else { // A variable appears more than others in the same equation, so its changes are going to propagate more.
          val indexBestVar = ids.indexOf(bestVar)
          val strings = if(indexBestVar == 0) { // Test only string prefixes or empty string
             (for{j <- (rhs.length to 1 by -1).toStream
                  if pos contains j} yield rhs.substring(0, j)) #:::
             (for{j <- (rhs.length to 1 by -1).toStream
                  if !(pos contains j)} yield rhs.substring(0, j)) #:::
              Stream("")
          } else {
            val lastIndexBestVar = ids.lastIndexOf(bestVar)
            if(lastIndexBestVar == ids.length - 1) {
               (for{ i <- pos.toStream // Try to maximize the size of the string from the start
                     if i != rhs.length
               } yield rhs.substring(i)) #:::
               Stream("")
            } else { // Inside, can be anything.
              (for{ i <- pos.toStream // Try to maximize the size of the string from the start
               if i != rhs.length
               j <- rhs.length to (i+1) by -1
               if pos contains j} yield rhs.substring(i, j)) #:::
               (for{ i <- pos.toStream
               if i != rhs.length
               j <- rhs.length to (i+1) by -1
               if !(pos contains j)} yield rhs.substring(i, j)) #:::
               Stream("")
            }
          }
          //println("Best variable:" + bestVar + " going to test " + strings.toList)
          
          for (str <- strings.distinct
               if java.util.regex.Pattern.quote(str).r.findAllMatchIn(rhs).length >= numBestVars
          ) yield {
            Map(bestVar -> str)
          }
        }
    }
  }
  
  @tailrec def statsStringForm(e: StringForm, acc: Map[Identifier, Int] = Map()): Map[Identifier, Int] = e match {
    case Nil => acc
    case Right(id)::q => statsStringForm(q, acc + (id -> (acc.getOrElse(id, 0) + 1)))
    case (_::q) => statsStringForm(q, acc)
  }
  
  @tailrec def stats(p: Problem, acc: Map[Identifier, Int] = Map()): Map[Identifier, Int] = p match {
    case Nil => acc
    case (sf, rhs)::q => 
      stats(q, (statsStringForm(sf) /: acc) { case (m, (k, v)) => m + (k -> (m.getOrElse(k, 0) + v)) })
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
      val current_buffer = ListBuffer[Identifier]()
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
    val (_, rhs) = minStatement
    val constants = minConstants
    val identifiers_grouped = minIdentifiersGrouped
    val statistics = stats(p)
    if(identifiers_grouped.length > 1) {
      // There might be different repartitions of the first boundary constant. We need to investigate all of them.
      repartitions(constants, rhs).map(_.head).distinct.toStream.flatMap(p => {
        val firstString = rhs.substring(0, p) // We only split on the first string.
        simpleSplit(identifiers_grouped.head, firstString)(statistics)
      })
    } else if(identifiers_grouped.length == 1) {
      simpleSplit(identifiers_grouped.head, rhs)(statistics) // All new assignments
    } else {
      if(rhs == "") Stream(Map()) else Stream.Empty
    }
  }
  
  /** Solves the problem and returns all possible satisfying assignment */
  def solve(p: Problem): Stream[Assignment] = {
    val realProblem = forwardStrategy.run(p, Map())
    /*if(realProblem.nonEmpty && realProblem.get._1.nonEmpty) {
      println("Problem:\n"+renderProblem(p))
      println("Solutions:\n"+realProblem.get._2)
      println("Real problem:\n"+renderProblem(realProblem.get._1))
    }*/
    
    realProblem match {
      case None => 
        Stream.Empty
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
  
  def variablesStringForm(sf: StringForm): Set[Identifier] = sf.collect { case Right(id) => id }.toSet
  def variables(gf: GeneralEquation): Set[Identifier] = variablesStringForm(gf._1) ++ variablesStringForm(gf._2)
  
  /** Returns true if the problem is transitively bounded */
  def isTransitivelyBounded(b: GeneralProblem, transitivelyBounded: Set[Identifier] = Set()): Boolean = {
    def isBounded(sf: GeneralEquation) = {
      variablesStringForm(sf._1).forall(transitivelyBounded) || variablesStringForm(sf._2).forall(transitivelyBounded)
    }
    val (bounded, notbounded) = b.partition(isBounded)
    
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
  
  
  ////////////////////////////////////////////////
  ////      Incremental problem extension     ////
  ////////////////////////////////////////////////
  
  /** Returns all subsets of i elements of a sequence. */
  def take[A](i: Int, of: Seq[A]): Stream[Seq[A]] = {
    if(i > of.size || i < 0) Stream.empty
    else if(i == of.size) Stream(of)
    else if(i == 0) Stream(Seq.empty)
    else {
      take(i - 1, of.tail).map(of.head +: _) #::: take(i, of.tail)
    }
  }
  
  /** For each variable from `ifVariable`, if it occurs only once, it will do nothing.
   *  If it occurs at least twice, it will first duplicate the problem with every but 1 occurrence of this variable set to its initialMapping.*/
  def keepEachOccurenceSeparatlyAndThenAllOfThem(p: Problem, ifVariable: Set[Identifier], initialMapping: Assignment): Stream[Problem] = {
    ifVariable.foldLeft(Stream(p)){
      case (problems, v) =>
        val c = count(s => s == Right(v))(p)
        if(c == 1) {
          problems
        } else {
          val originalValue = initialMapping(v)
          for{p <- problems
              i <- (1 to c).toStream} yield {
            var index = 0
            map{ case r@Right(`v`) =>
              index += 1
              if(index != i) Left(originalValue) else r
            case e => e}(p)
          }
        }
    }
  }
  
  /** If the stream is not empty and there are more than two variables,
   *  it will try to assign values to variables which minimize changes.
   *  It will try deletions from the end and from the start of one variable.
   * */
  def minimizeChanges(s: Stream[Assignment], p: Problem, ifVariable: Set[Identifier], initialMapping: Assignment): Stream[Assignment] = {
    if(s.isEmpty || ifVariable.size <= 1) s else {
      ((for{v <- ifVariable.toStream
          originalValue = initialMapping(v)
          i <- originalValue.length to 0 by -1
          prefix <- (if(i == 0 || i == originalValue.length) List(true) else List(true, false))
          possibleValue = (if(prefix) originalValue.substring(0, i) else originalValue.substring(originalValue.length - i))
          s <- solve(reduceProblem(Map(v -> possibleValue))(p))
         } yield s + (v -> possibleValue)) ++ s).distinct
    }
  }
  
  /** Solves the problem while supposing that a minimal number of variables have been changed.
   *  Will try to replace variables from the left first.
   *  If a variable occurs multiple times, will try to replace each of its occurrence first.
   *  */
  def solveMinChange(p: Problem, initialMapping: Assignment): Stream[Assignment] = {
    // First try to see if the problem is solved. If yes, returns the initial mapping
    val initKeys = initialMapping.keys.toSeq
    for{
      i <- (0 to initialMapping.size).toStream
      toReplace <- take(i, initKeys)
      ifVariable = toReplace.toSet
      newProblems = reduceProblem(initialMapping filterKeys (x => !ifVariable(x)))(p)
      newProblem <- keepEachOccurenceSeparatlyAndThenAllOfThem(newProblems, ifVariable, initialMapping)
      solution <- minimizeChanges(solve(newProblem), newProblem, ifVariable, initialMapping: Assignment)
    } yield solution
  }
}