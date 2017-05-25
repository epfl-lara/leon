package leon.synthesis.comfusy

//dummy
object APAInputAssignments 

/** This object offers global methods methods to deal with input assignments. 
 */
object InputAssignment {
  //Combines input sentences
  def listToCommonString(input_assignment:List[InputAssignment], indent:String):String = {
    val prog_input = input_assignment map (_.toCommonString(indent)) match {
      case Nil => ""
      case l => l reduceLeft {(t1, t2) => (t1 + "\n" + t2)}
    }
    prog_input
  }
}

/** An input assignment is a way to assign some expressions to input variables
 *  like in "val a = b/2+c", where a, b and c are input variables.
 */
sealed abstract class InputAssignment {

  /** Returns a list of input variables contained in the expression of this input assignment */
  def input_variables: List[InputVar]
  
  /** Extracts a non-exhaustive list of simple assignments of InputTerms to InputVars. */
  def extract:List[(InputVar, APAInputTerm)]
  
  /** Returns a string representing this assignment under the current rendering mode.  */
  def toCommonString(indent: String):String = APASynthesis.rendering_mode match {
    case RenderingScala => toScalaString(indent)
    case RenderingPython => toPythonString(indent)
  }
  
  /** Returns a scala string representing the variables on the left of <code>val ... = ...</code> */
  def varToScalaString = this match {
    case SingleInputAssignment(i, t) => i.name
    case BezoutInputAssignment(vl, tl) => "List(" + (vl map { l => "List(" + (l map (_.name) reduceLeft (_+","+_)) + ")"} reduceLeft (_+","+_)) + ")"
  }
  
  /** Returns a scala string representing the value on the right of <code>val ... = ...</code> */
  def valToScalaString = this match {
    case SingleInputAssignment(i, t) => t
    case BezoutInputAssignment(vl, tl) => "Common.bezoutWithBase(1, "+(tl map (_.toString) reduceLeft (_+", "+_))+")"
  }
  
  /** Returns a python string representing the variables on the left of <code>val ... = ...</code> */
  def varToPythonString = this match {
    case SingleInputAssignment(i, t) => i.name
    case BezoutInputAssignment(vl, tl) => "(" + (vl map { l => "(" + (l map (_.name) reduceLeft (_+","+_)) + ")"} reduceLeft (_+","+_)) + ")"
  }
  
  /** Returns a python string representing the value on the right of <code>val ... = ...</code> */
  def valToPythonString = this match {
    case SingleInputAssignment(i, t) => t
    case BezoutInputAssignment(vl, tl) => "bezoutWithBase(1, "+(tl map (_.toString) reduceLeft (_+", "+_))+")"
  }
  
  /** Returns the whole assignment as a scala string */
  def toScalaString(indent: String): String =  {
    indent+"val "+ varToScalaString + " = " + valToScalaString
  }
  
  /** Returns the whole assignment as a python string */
  def toPythonString(indent: String): String = {
    indent+ varToPythonString + " = " + valToPythonString
  }
  
  /** Returns the assignment were all input variables have been replaced by corresponding input terms. */
  def replaceList(l : List[(InputVar, APAInputTerm)]):List[InputAssignment]
  
  /** Returns the assignment were the sign abstraction s is applied to each occurence of t1 */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):InputAssignment
}

// A simple assignment corresponding to <code>val v = t</code>
case class SingleInputAssignment(v: InputVar, t: APAInputTerm) extends InputAssignment {
  def input_variables = List(v)
  def extract = List((v, t))
  def replaceList(l : List[(InputVar, APAInputTerm)]) = List(SingleInputAssignment(v, t.replaceList(l)))
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction) = SingleInputAssignment(v, t.assumeSignInputTerm(t1, s))
}
// A complex Bézout assignemnt corresponding to <code>val (v1::v2::Nil)::(v3::v4::Nil)::Nil = Common.bezoutWithBase(1, t1, t2)</code> 
case class BezoutInputAssignment(v: List[List[InputVar]], t: List[APAInputTerm]) extends InputAssignment {
  def input_variables = v.flatten : List[InputVar]
  def extract = Nil
  def replaceList(l: List[(InputVar, APAInputTerm)]) = BezoutInputAssignment(v, t map (_.replaceList(l))).simplified
  
  /** Returns a simplified version of the assignment as a list of input assignments. */
  /** Simplification occurs if some coefficients are equal to 1 or -1, or in other simple cases. */
  def simplified: List[InputAssignment] = {
    t map (_.simplified) match {
      case t if t forall {
            case APAInputCombination(i, Nil) => true
            case _ => false
          } =>
        val bezout_coefs:List[Int] = t map {
          case APAInputCombination(i, Nil) => i
          case t => throw new Exception("Theoretically unreachable section : "+t+" should be an integer")
        }
        // Double zip and add all assignments to variables
        val assignments: List[(InputVar, APAInputTerm)] = (
            (v zip Common.bezoutWithBase(1, bezout_coefs)) map {
              case (l1, l2) => l1 zip (
                l2 map {
                  case i => APAInputCombination(i)
                }
              )
            }
          ).flatten
        val assignment_converted = assignments.map({ case (v, t) => SingleInputAssignment(v, t)})
        assignment_converted 
      case a::Nil => // This corresponds to equations of the type 1+a*v = 0. If there is a solution, it is exactly -a (a has to be equal to 1 or -1)
        val List(List(iv)) = v
        List(SingleInputAssignment(iv, -a))
      case a::b::Nil => // This corresponds to equations of the type 1+a*u+b*v = 0
        // There is an optimization if either a or b has an absolute value of 1.
        (a, b) match {
          case (APAInputCombination(i, Nil), b) if Math.abs(i) == 1 =>
            // case 1 + i*u + a*v == 0
            val index_b = 2
            var map_index_term = Map[Int, APAInputTerm]() + (index_b -> b)
            val new_ints = Common.bezoutWithBase(1, i, index_b)
            val assignments = convertAssignments(v, new_ints, map_index_term)
            val assignment_converted = assignments.map({ case (v, t) => SingleInputAssignment(v, t)})
            assignment_converted
          case (a, APAInputCombination(j, Nil)) if Math.abs(j) == 1 =>
            val index_a = 2
            var map_index_term = Map[Int, APAInputTerm]() + (index_a -> a)
            val new_ints = Common.bezoutWithBase(1, index_a, j)
            val assignments = convertAssignments(v, new_ints, map_index_term)
            val assignment_converted = assignments.map({ case (v, t) => SingleInputAssignment(v, t)})
            assignment_converted
          case _ => List(BezoutInputAssignment(v, t)) 
        }
      case t =>
        val t_indexed = t.zipWithIndex 
        t_indexed find { 
          case (APAInputCombination(i, Nil), index) if Math.abs(i) == 1 => true
          case _ => false
        } match {
          case Some((APAInputCombination(one_coefficient, Nil), index)) =>
            // Corresponds to something trivial like 1 + a*x + b*y + z + c*w = 0
            // The corresponding assignment is x = y1, y = y2, z = -1-a*x-b*y-c*w and w = y3
            //  (1 )T  (0, 0, -1, 0)   (a)
            //  (ya) . (1, 0, -a, 0) . (b)  + 1  == 0
            //  (yb)   (0, 1, -b, 0)   (1)
            //  (yc)   (0, 0, -c, 1)   (c)
            
            // To find the solution, encode a = 10, b = 20, c=30, and in the found solution, replace -10 by -a, etc.
            var map_index_term = Map[Int, APAInputTerm]()
            
            val to_solve_bezout_on = t_indexed map { case (term, i) =>
              if(i == index) {
                one_coefficient
              } else {
                val final_index = 10*i+10
                map_index_term += (final_index -> term)
                final_index
              }
            }
            val new_ints = Common.bezoutWithBase(1, to_solve_bezout_on)
            val assignments = convertAssignments(v, new_ints, map_index_term)
            val assignment_converted = assignments.map({ case (v, t) => SingleInputAssignment(v, t)})
            assignment_converted
          
          case _ => // Essentially None
            List(BezoutInputAssignment(v, t)) 
        }
    }
  }
  
  /** Converts an integer Bézout solution to a InputTerm solution, where specific integers */
  /** given in map_index_terms are replaced with some input terms. */
  def convertAssignments(v: List[List[InputVar]],
                         solved_for_ints: List[List[Int]],
                         map_index_term:  Map[Int, APAInputTerm]): List[(InputVar, APAInputTerm)] = {
    (
      (v zip solved_for_ints) map {
        case (l1, l2) => l1 zip (
          l2 map {
            case index if map_index_term contains index => 
              map_index_term(index)
            case index if map_index_term contains (-index) =>
              -map_index_term(index)
            case i =>
              APAInputCombination(i)
          }
        )
      }
    ).flatten
  }
  
  /** Propagate a sign assumption. Does nothing for Bézout assignment. */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction) = this
}
