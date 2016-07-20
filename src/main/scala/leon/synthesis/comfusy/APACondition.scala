package leon.synthesis.comfusy

/** An abstract precondition or specification representation.
 *  Such preconditions are commonly associated to a program which correctly executes if the condition is true.
 *
 *  @author  Mikaël Mayer
 */
sealed abstract class APAAbstractCondition {

  /** Returns a string representing the condition in current rendering mode.
   *  See APASynthesis.rendering_mode to change it. */
  def toCommonString : String

  /** Returns the boolean value of this condition under a certain variable mapping. */
  def execute(l: Map[InputVar, Int]): Boolean

  /** Returns the list of input variables contained in this conditions.   */
  def input_variables: List[InputVar]
}


/** This object provides optimization and default values for conditions.
 *
 *  @author  Mikaël Mayer
 */
object APACondition {

  /** Returns a typical false precondition. */
  def False: APACondition = APACondition(Nil, APAFalse(), APAEmptySplitCondition())

  /** Creates a new APACondition after optimizing the arguments
   *
   *  @param input_assignment The list of input assignments to change if necessary.
   *  @param global_condition A simple formula part of the condition.
   *  @param pf An advanced formula part of the condition (bounded quantifiers, disjunction of other conditions...)
   *  @return An optimized APACondition.
   */
  def optimized(input_assignment: List[InputAssignment], global_condition: APAFormula, pf : APASplitCondition):APACondition = {
    val final_input_variables = (global_condition.input_variables ++ pf.input_variables).distinct
    val (useful_input_assignments, _) = input_assignment.foldRight((Nil:List[InputAssignment], final_input_variables:List[InputVar])) {
      case (assignment@SingleInputAssignment(x, t), (useful_input_assignments, useful_input_variables)) =>
        if(useful_input_variables contains x) { // Then it's useful
          (assignment::useful_input_assignments, t.input_variables ++ useful_input_variables)
        } else { // Then this variable is useless
          (useful_input_assignments, useful_input_variables)
        }
      case (assignment@BezoutInputAssignment(xl, tl), (useful_input_assignments, useful_input_variables)) =>
        if((xl.flatten : List[InputVar]) exists (useful_input_variables contains _)) { // Then it's useful
          (assignment::useful_input_assignments, (tl flatMap (_.input_variables)) ++ useful_input_variables)
        } else { // Then this variable is useless
          (useful_input_assignments, useful_input_variables)
        }
    }
    if(global_condition == APAFalse()) return APACondition.False
    val result = if(pf.input_variables == Nil) {
      pf.execute(Map()) match {
        case false => APACondition.False
        case true => APACondition(useful_input_assignments, global_condition.simplified, APAEmptySplitCondition())
      }
    } else {
      global_condition.simplified match {
        case t@APAFalse() => APACondition(useful_input_assignments, t, APAEmptySplitCondition())
        case t => APACondition(useful_input_assignments, t, pf)
      }
    }
    result
  }
}

/** Class representing a program precondition.
 *
 *  @param input_assignment The list of input assignments to change if necessary.
 *  @param global_condition A simple formula part of the condition.
 *  @param pf An advanced formula part of the condition (bounded quantifiers, disjunction of other conditions...)
 *  @author  Mikaël Mayer
 */
case class APACondition(input_assignment: List[InputAssignment], global_condition: APAFormula, pf : APASplitCondition) extends APAAbstractCondition {

  /** Adds an assumption after the existing assumptions and before the advanced formula. */
  def &&(more_cond: APAFormula):APACondition = APACondition(input_assignment, global_condition && more_cond, pf)

  /** Adds an assumption before the existing assumptions.
   *  Used e.g. in the case a condition a % b == 0  if b != 0 is checked before.
   */
  def assumeBefore(more_cond: APAFormula):APACondition = APACondition(input_assignment, more_cond && global_condition, pf)

  /** Returns if the condition is trivially true. */
  def isTrivial(): Boolean = global_condition == APATrue() && pf == APAEmptySplitCondition()

  /** Returns the list of the input variables appearing anywhere in the precondition */
  def input_variables = ((global_condition.input_variables ++ pf.input_variables) filterNot ((input_assignment flatMap (_.input_variables))).contains).distinct

  /** Returns a parsable string representing the body of the condition, without variable assignment,
   *  under the current rendering mode. */
  protected def conditionBodyToCommonString(rm: RenderingMode) = (global_condition, pf) match {
    case (_, APAEmptySplitCondition()) => global_condition.toString
    case (APATrue(), _) => pf.toString
    case _ => "("+global_condition.toString+") "+rm.and_symbol+" ("+pf.toString+")"
  }

  /** Returns a parsable string representing the complete condition */
  def conditionToCommonString = APASynthesis.rendering_mode match {
    case RenderingScala => conditionToScalaString
    case RenderingPython => conditionToPythonString
  }

  /** Returns a parsable scala string representing the complete condition */
  def conditionToScalaString = input_assignment match {
    case Nil => conditionBodyToCommonString(APASynthesis.rendering_mode)
    case _ => "{"+(input_assignment map (_.toCommonString("")) reduceLeft (_+";"+_)) + ";"+conditionBodyToCommonString(APASynthesis.rendering_mode)+"}"
  }

  /** Returns a parsable python string representing the complete condition */
  def conditionToPythonString = {
    def conditionToPythonString_aux(input_assignment: List[InputAssignment]):String = input_assignment match {
      case Nil => conditionBodyToCommonString(APASynthesis.rendering_mode)
      case (assignment::q) =>
        "(lambda "+assignment.varToPythonString+": "+conditionToPythonString_aux(q)+")("+assignment.valToPythonString+")"
    }
    conditionToPythonString_aux(input_assignment)
  }

  /** toString alias */
  def toCommonString = conditionToCommonString

  /** toString alias */
  override def toString = toCommonString

  def execute(l: Map[InputVar, Int]): Boolean = {
    var input_value_map = l
    input_assignment foreach {
      case SingleInputAssignment(v, t) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
      t.replaceList(input_value_assignment) match {
        case APAInputCombination(i, Nil) => input_value_map += (v -> i)
        case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
      }
      case BezoutInputAssignment(vl, tl) => val input_value_assignment = APAAbstractProgram.toAPAInputAssignment(input_value_map)
        val bezout_coefs:List[Int] = tl map (_.replaceList(input_value_assignment)) map {
          case APAInputCombination(i, Nil) => i
          case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+input_value_map)
        }
        // Double zip and add all assignments to variables
        (vl zip Common.bezoutWithBase(1, bezout_coefs)) map { case (l1, l2) => l1 zip l2 } foreach { _ foreach { input_value_map += _ } }
    }
    global_condition.replaceListInput(APAAbstractProgram.toAPAInputAssignment(input_value_map)) match {
      case APATrue() => pf.execute(input_value_map)
      case APAFalse() => false
      case t =>
        throw new Exception ("Could not find the truth value of "+this+"\n under the mapping "+input_value_map+".\n Got the result: "+t)
    }
  }
}

/** Advanced conditions.
 *  @author Mikaël Mayer
 */
sealed abstract class APASplitCondition extends APAAbstractCondition {

  /** Returns a string representing the condition. */
  override def toString = toStringGeneral(APASynthesis.rendering_mode)

  /** Method to override. Return astring representing the solution under the given RenderingMode */
  protected def toStringGeneral(rm: RenderingMode):String

  /** Alias for toString */
  def toCommonString:String = toStringGeneral(APASynthesis.rendering_mode)
}

/** Disjunction of all conditions.
 *  c1 || c2 || c3 ...
 *  It is named CaseSplit because the condition is derived from a sequence of if-then-else statements/
 *  if(c1) ... else if(c2) ... else if(c3) ...
 *
 *  @author Mikaël Mayer
 */
case class APACaseSplitCondition(csl: List[APAAbstractCondition]) extends APASplitCondition {

  /** Returns the list of the input variables contained in this disjunction */
  def input_variables = (csl flatMap (_.input_variables)).distinct

  /** Returns a boolean indicating if the disjunction is true. */
  def execute(l: Map[InputVar, Int]): Boolean = csl exists (_.execute(l))

  /** Returns a string representing this disjunction. */
  protected def toStringGeneral(rm: RenderingMode):String = csl map { t => ("("+(t.toCommonString)+")") } reduceLeft (_ + " "+rm.or_symbol+" " + _)

  /** Returns a condition made from this disjunction. */
  def toCondition: APACondition = APACondition(Nil, APATrue(), this)
}

/** Empty advanced condition
 *  Equivalent to a true precondition.
 *
 *  @author Mikaël Mayer
 */
case class APAEmptySplitCondition() extends APASplitCondition {

  /** Returns the empty set of input variables. */
  def input_variables = Nil

  /** Returns true, the truth value of this expression */
  def execute(l: Map[InputVar, Int]): Boolean = true

  /** Returns an empty string, which represents an empty condition. */
  protected def toStringGeneral(rm: RenderingMode) = ""
}

/** Bounded quantifier representation.
 *  The variable vector will iterate over [lower_range, upper range]^n where n is the number of variables.
 *  The provided global condition is implicitly existentially quantified over this bounded variable vector.
 *  To sum up, the condition is true if global_condition holds for one tuple in the hypercube
 *
 *  @param vl A list of input variables (v1...vn)
 *  @param lower_range The lower range for each variable.
 *  @param upper_range The upper range for each variable.
 *  @param global_condition The implicitly existentially quantified over the variables.
 *  @author Mikaël Mayer
 */
case class APAForCondition(vl: List[InputVar], lower_range: APAInputTerm, upper_range: APAInputTerm, global_condition: APACondition) extends APASplitCondition {

  /** Returns the list of input variables in this condition, not part of the existentially quantified variables. */
  def input_variables = (global_condition.input_variables) filterNot (vl.contains)

  /** Returns a string representing the bounded quantified condition in a programming language. */
  protected def toStringGeneral(rm: RenderingMode):String = {
    rm match {
      case RenderingScala => toScalaString
      case RenderingPython => toPythonString
    }
  }

  /** Returns a string containing the tuple of the existential variable's names */
  def varsToString(vl : List[InputVar]) : String = vl match {
    case Nil => ""
    case (v::Nil) => v.name
    case (v::q) => "("+v.name+","+varsToString(q)+")"
  }

  /** Returns a python string representing the condition */
  def toPythonString:String = {
    val basic_range = "xrange("+lower_range+", 1 + "+upper_range+")"
    val list_ranges = "("+varsToString(vl)+" "+ (vl map { case i => "for "+i.name+" in "+basic_range}).reduceLeft(_ + " " + _) + ")"
    val exists_construct = "lambda a, "+varsToString(vl)+": a or "+ global_condition.toCommonString
    val condition = "reduce("+exists_construct+", "+list_ranges+", False)"
    condition
  }

  /** Returns a scala string representing the condition */
  def toScalaString:String = {
    val basic_range = "("+lower_range+" to "+upper_range+")"
    var ranges = basic_range
    vl.tail foreach {k =>
      ranges = ranges + " flatMap { t => "+basic_range+" map { i => (i, t) } } "
    }

    val expanded_vars = varsToString(vl)
    val find_string = ranges + " exists { case "+expanded_vars+" => "
    val cond_string = global_condition.toCommonString
    val match_string = " }"
    (find_string::cond_string::match_string::Nil).reduceLeft((_ + _))
  }

  /** Returns a boolean indicating if the condition is true under a given mapping */
  def execute(l: Map[InputVar, Int]): Boolean = {
    if(global_condition == APACondition.False) return false
    val lr:Int = lower_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t => throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val ur:Int = upper_range.replaceList(APAAbstractProgram.toAPAInputAssignment(l)) match {
      case APAInputCombination(k, Nil) => k
      case t =>
        throw new Exception("Was not able to reduce term "+t+" to integer under the mapping "+l)
    }
    val basic_range = (lr to ur)
    def possible_assignments(vl: List[InputVar], i: Int, current_assignment: List[(InputVar, Int)]) : Stream[List[(InputVar, Int)]] = vl match {
      case Nil => Stream(current_assignment)
      case (v::q) if i > ur => Stream()
      case (v::q) => possible_assignments(q, lr, (v, i)::current_assignment) append possible_assignments(vl, i+1, current_assignment)
    }
    val assignments = possible_assignments(vl, lr, Nil)

    assignments exists { assignments =>
      global_condition.execute(l ++ assignments)
    }
  }
}
