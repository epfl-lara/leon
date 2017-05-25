package leon.synthesis.comfusy
//import scala.annotation.tailrec

//*********************************** Pressburger Synthesis ************************************************//

sealed abstract class RenderingMode {
  val true_symbol:String
  val false_symbol:String
  val and_symbol: String
  val or_symbol:String
  val not_symbol:String
  val min_symbol: String
  val max_symbol: String
  val error_string: String
  val abs_symbol: String
  val gcd_symbol: String
  val lcm_symbol: String
  def mod_function(operand: String, divisor: String): String
}

case object RenderingScala extends RenderingMode {
  val (true_symbol, false_symbol, and_symbol, or_symbol, not_symbol, min_symbol, max_symbol, error_string) =
    ("true", "false", "&&", "||", "!", "Math.min", "Math.max", "throw new Error(\"No solution exists\")")
  val (abs_symbol, gcd_symbol, lcm_symbol) = ("Math.abs", "Common.gcdlist", "Common.lcmlist")
  def mod_function(string_numerator: String, denominator: String): String = {
    if(APASynthesis.advanced_modulo)
       string_numerator+"%%"+denominator
    else
      "("+denominator+" + "+string_numerator+"%"+denominator+")%"+denominator

  }
}

case object RenderingPython extends RenderingMode {
  val (true_symbol, false_symbol, and_symbol, or_symbol, not_symbol, min_symbol, max_symbol, error_string) =
    ("True", "False", "and", "or", "not", "min", "max", "raise Exception(\"No solution exists\")")
  val (abs_symbol, gcd_symbol, lcm_symbol) = ("abs", "gcd", "lcm")
  def mod_function(operand: String, divisor: String): String = {
    operand+"%" + divisor
 }
}

object APASynthesis {
  /* ************* Synthesis options *************** */
  /** Rendering expressions of the form a %% b where a %% 0 == a,  and else (k %% b) is always between 0 and b-1 and congruent to k modulo b. */
  var advanced_modulo = false

  /** To turn off run-time checks : if true, the "throw new Error" are replaced by tuples filled with zeros. */
  var run_time_checks = false

  /** top-level rendering mode for toString */
  var rendering_mode:RenderingMode = RenderingScala

  // ************* Different ways of specifying solving conditions ***************/** */

  /** Returns all output variables in the given list of equations */
  def getOutputVariables(eqs: List[APAEquation]):List[OutputVar] = {
    (eqs flatMap (_.output_variables)).distinct
  }

  /** Solve the equations in a lazy way */
  def solveLazyEquations(input_variables: List[InputVar], output_variables: List[OutputVar], eqslazy: FormulaSplit):(APACondition, APAProgram) = {
    return (new APASynthesis(eqslazy, input_variables, output_variables)).solve()
  }

  def solveLazyEquations(name: String, output_variables: List[OutputVar], eqs: APAFormula):(APACondition, APAProgram) = {
    val input_variables = eqs.input_variables
    var (cond, prog) = (new APASynthesis(eqs.getLazyEquations, input_variables, output_variables)).solve()
    prog.setName(name)
    (cond, prog)
  }

  /*def solveEquations(name: String, variables: List[OutputVar], eqs: List[APAEquation]) = {
    var (cond, prog) = (new APASynthesis(eqs, variables)).solve()
    prog.setName(name)
    (cond, prog)
  }*/

  def solve(name: String, output_variables: List[OutputVar], formula_sequence: APAFormula*):(APACondition, APAProgram) = {
    val formula = APAConjunction(formula_sequence.toList).simplified
    //val dnf:Stream[List[APAEquation]] = formula.getEquations
    //val output_variables = variables
    //val input_variables = formula.input_variables
    //val programs_conditions = (dnf map {solveEquations("", output_variables, _)}).toList
    solveLazyEquations(name, output_variables, formula)
  }
  def solve(name: String, formula_sequence: APAFormula*):(APACondition, APAProgram) = {
    solve(name, formula_sequence.toList)
  }
  def solve(name: String, formula_sequence: List[APAFormula]):(APACondition, APAProgram) = {
    val formula = APAConjunction(formula_sequence.toList).simplified
    solve(name, formula.output_variables, formula)
  }
  def solve(variables:List[OutputVar], formula_sequence: APAFormula*):(APACondition, APAProgram) = {
    solve(variables, formula_sequence.toList)
  }
  def solve(variables:List[OutputVar], formula_sequence: List[APAFormula]):(APACondition, APAProgram) = {
    val formula = APAConjunction(formula_sequence.toList).simplified
    solve("result", variables, formula)
  }
  def solve(formula_sequence: APAFormula*):(APACondition, APAProgram) = {
    solve(formula_sequence.toList)
  }
  def solve(formula_sequence: List[APAFormula]):(APACondition, APAProgram) = {
    val formula = APAConjunction(formula_sequence).simplified
    solve("result", formula.output_variables, formula)
  }


  /** ************* Function used in the algorithm *************** */
  val alphabet = "abcdefghijklmnopqrstuvwxyz"
  def newOutputVariable(input_existing: List[InputVar], output_existing : List[OutputVar]): OutputVar = {
    //var typical = "xyzmnpqrstuvw"
    var i = 0
    val names = (input_existing map (_.name)) ++ (output_existing map (_.name))
    (0 to 25) foreach { i =>
      val test = "y"+alphabet.substring(i, i+1)
      if(!(names contains test))
        return OutputVar(test)
    }
    while(names contains ("y"+i)) {
      i+=1
    }
    OutputVar("y"+i)
  }
  def newInputVariable(input_existing: List[InputVar], output_existing : List[OutputVar]): InputVar = {
    var i = 0
    val names = (input_existing map (_.name)) ++ (output_existing map (_.name))
    while(names contains ("k"+i)) {
      i+=1
    }
    InputVar("k"+i)
  }

  // Split the list into APAEqualZero one left and not APAEqualZero on right
  def partitionPAEqualZero(eqs : List[APAEquation]):(List[APAEqualZero], List[APAEquation]) = eqs match {
    case Nil => (Nil, Nil)
    case (p@APAEqualZero(pac)::q) =>
      val (a, b) = partitionPAEqualZero(q)
      (APAEqualZero(pac)::a, b)
    case (p::q) =>
      val (a, b) = partitionPAEqualZero(q)
      (a, p::b)
  }
  // Splits the list into equalities, inequalities, and a boolean indicating if the system is consistent.
  def partitionPAGreaterEqZero(eqs : List[APAEquation]):(List[APAEqualZero], List[APAGreaterEqZero], Boolean) = eqs match {
    case Nil => (Nil, Nil, true)
    case (p@APAEqualZero(pac)::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (APAEqualZero(pac)::a, b, c)
    case (p@APAGreaterEqZero(pac)::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (a, APAGreaterEqZero(pac)::b, c)
    case (p@APAGreaterZero(APACombination(coef, o))::q) =>
      val (a, b, c) = partitionPAGreaterEqZero(q)
      (a, APAGreaterEqZero(APACombination(coef+APAInputCombination(-1), o))::b, c)
    case (APATrue()::q) =>
      partitionPAGreaterEqZero(q)
    case (APAFalse()::q) =>
      (Nil, Nil, false)
    case (APADivides(n, pac)::q) =>
      throw new Error("Divides are not supported at this point")
  }


  def recursive_propagation(
      output_assignments : List[(OutputVar, APATerm)],
      assignments_to_propagate : List[(OutputVar, APACombination)],
      interesting_variables : List[OutputVar])
        : List[(OutputVar, APATerm)]  =
      output_assignments match {
    case Nil => Nil
    case (v, pac@APACombination(_, _))::q => pac.replaceList(assignments_to_propagate) match {
      case pac@APACombination(APAInputCombination(_, Nil), Nil) => // We propagate constants
        if(interesting_variables contains v) {
          (v, pac)::recursive_propagation(q, (v,pac)::assignments_to_propagate, interesting_variables)
        } else {
          recursive_propagation(q, (v,pac)::assignments_to_propagate, interesting_variables)
        }
      case t => (v, t)::recursive_propagation(q, assignments_to_propagate, interesting_variables)
    }
    case (v, t)::q => (v, t.replaceList(assignments_to_propagate))::recursive_propagation(q, assignments_to_propagate, interesting_variables)
  }

  // Propagate simple assignments, by removing the introduced variables if possible.
  def propagateAssignment(y: OutputVar, t: APACombination, output_assignments : List[(OutputVar, APATerm)], output_variables_initial : List[OutputVar]): List[(OutputVar, APATerm)]  = {
    recursive_propagation(output_assignments, (y,t)::Nil, output_variables_initial)
  }
  
  def needsLessOperations(coef1: APAInputTerm, coef2: APAInputTerm): Boolean = (coef1, coef2) match {
    case (APAInputCombination(k1, Nil), APAInputCombination(k2, Nil)) => Math.abs(k1) < Math.abs(k2)
    case (APAInputCombination(k1, Nil), _) => true
    case (_, APAInputCombination(k2, Nil)) => false
    case (_, _) => false
  }
  
  def minInputTerms(coef1: APAInputTerm, coef2:APAInputTerm) = if(needsLessOperations(coef1, coef2)) coef1 else coef2

  /** Sorting function (OptimizeMe) */
  /** Priority to constant terms */
  def by_least_outputvar_coef(eq1: APAEqualZero, eq2: APAEqualZero): Boolean = (eq1, eq2) match {
    case (APAEqualZero(pac1@APACombination(c1, o1)), APAEqualZero(pac2@APACombination(c2, o2))) =>
      val min_coefs_o1 = o1 map (_._1) reduceLeft (minInputTerms(_, _))
      val min_coefs_o2 = o2 map (_._1) reduceLeft (minInputTerms(_, _))
      needsLessOperations(min_coefs_o1, min_coefs_o2)
  }
}

class APASynthesis(equations: FormulaSplit, input_variables_initial:List[InputVar], output_variables_initial:List[OutputVar]) {
  import APASynthesis._
  var output_variables:List[OutputVar] = output_variables_initial
  var output_variables_encountered:List[OutputVar]  = output_variables_initial

  var input_variables:List[InputVar]  = input_variables_initial
  var input_variables_encountered:List[InputVar]  = input_variables_initial

  // Global_precondition is a conjunction of disjunctions of conjunctions.
  var global_precondition: List[APAFormula] = Nil
  // equation should not have output variables
  def addPrecondition (e: APAFormula):Unit    = {
    val f = e.simplified
    if(f.output_variables != Nil) // Debug sentence
        throw new Exception("Error: there should be no output variables in this precondition :"+f)
    f match {
      case APATrue() =>
      case APAFalse() => setFalsePrecondition()
      case APAConjunction(l) => l foreach (addPrecondition(_))
      case APAGreaterEqZero(APACombination(i, Nil)) => // We forward the constraint.
        input_assignments = input_assignments map { case assignment =>
          assignment.assumeSignInputTerm(i, PositiveZeroSign())
        }
        output_assignments = output_assignments map {
          case (v, t) =>
            (v, t.assumeSignInputTerm(i, PositiveZeroSign()))
        }
        global_precondition = f :: global_precondition
      case f =>
        global_precondition = f :: global_precondition
    }
  }
  def setFalsePrecondition() = global_precondition = APAFalse()::Nil
  def addOutputVar(y: OutputVar) = {
    output_variables = (y::output_variables)
    output_variables_encountered = (y::output_variables_encountered). distinct
  }
  def delOutputVar(y: OutputVar) = output_variables = output_variables.filterNot(_ == y)
  def addInputVar (y: InputVar)  = {
    input_variables = (y::input_variables)
    input_variables_encountered = (y::input_variables_encountered)
  }
  def getNewOutputVarWithoutRegistering() = APASynthesis.newOutputVariable(input_variables_encountered, output_variables_encountered)
  def getNewOutputVar() = {
    val y = getNewOutputVarWithoutRegistering()
    addOutputVar(y)
    y
  }
  def getNewInputVar() = {
    val x = APASynthesis.newInputVariable(input_variables_encountered, output_variables_encountered)
    addInputVar(x)
    x
  }
  // List of reversed assignments: At the end, leftmost assignments should be done at the end.
  var input_assignments: List[InputAssignment] = Nil
  var output_assignments: List[(OutputVar, APATerm)] = Nil
  def addSingleInputAssignment (x: InputVar,  t: APAInputTerm) = input_assignments  = input_assignments ++ (SingleInputAssignment(x, t.simplified)::Nil)
  def addBezoutInputAssignment (xl: List[List[InputVar]],  tl: List[APAInputTerm]) = input_assignments  = input_assignments ++ (BezoutInputAssignment(xl, tl).simplified)
  def addOutputAssignment(y: OutputVar, t: APATerm) = output_assignments = (y, t.simplified)::output_assignments
  def removeInputAssignment(y: InputVar) = input_assignments = input_assignments filterNot {case SingleInputAssignment(x, _) if x == y => true; case _ => false}
  /************* Functions used in the algorithm *************** */
  def simplifyEquations(equations: List[APAEquation]) : List[APAEquation] = {
    equations flatMap {
      case e@APADivides(k, APACombination(c, Nil)) =>
        addPrecondition(e.simplified)
        Nil
      case APADivides(k, APACombination(c, o)) =>
        val y = getNewOutputVar()
        APAEqualZero(APACombination(c, (k, y)::o)).simplified::Nil
      case APAGreaterZero(APACombination(c, o)) => APAGreaterEqZero(APACombination(c-APAInputCombination(1), o)).simplified::Nil
      case e => e.simplified::Nil
    }
  }
  
  /** Returns the remaining non_equalities (non_equalities should not contain equalities, nor will the returned term do) */
  def solveEqualities(data: FormulaSplit): APASplit = {
    val FormulaSplit(equalities, non_equalities, remaining_disjunctions) = data

    /** Make sure all equalities have at least one output variable, else remove them. */
    val (interesting_equalities, precondition_equalities) = equalities partition (_.has_output_variables)
    addPrecondition(APAConjunction(precondition_equalities))

    val sorted_equalities = interesting_equalities sortWith by_least_outputvar_coef

    sorted_equalities match {
      case Nil =>
        val newfs = FormulaSplit(Nil, non_equalities, remaining_disjunctions)
        solveEquations(newfs)
      case (eq1@APAEqualZero(pac@APACombination(c1, o1)))::rest_equalities =>
        var const_part:APAInputTerm = c1
        var o1_coefs = o1 map (_._1)
        var o1_vars = o1 map (_._2)
        val gcd = APAInputGCD(o1_coefs).replaceList(input_assignments flatMap (_.extract)).simplified

        gcd match {
          case APAInputCombination(1, Nil) =>
            // Perfect !! We know that there is a solution.
            // Continue to CONTINUE_POINT
          case n =>
            val coefs_are_zero = APAConjunction(o1_coefs map (APACombination(_)===APAInputCombination(0))).simplified
            if(coefs_are_zero == APATrue() || pac.allCoefficientsAreZero) {
              // We add the precondition const_part == 0
              addPrecondition(APACombination(const_part)===APAInputCombination(0))
              return solveEqualities(FormulaSplit(rest_equalities, non_equalities, remaining_disjunctions))
            } else if(coefs_are_zero == APAFalse() || pac.notAllCoefficientsAreZero) {
              // Regular run. We know that the GCD of the numbers is positive.
              addPrecondition(APADivides(n, APACombination(const_part, Nil)))
              val x = getNewInputVar()
              val n_positive = n.assumeSign(1)
              val gcd_expr = n_positive match {
                case APAInputCombination(i, Nil) =>
                  n_positive
                case APAInputCombination(0, ((k, _)::Nil)) if Math.abs(k) == 1 =>
                  n_positive
                case _ =>
                  val gcd_var = getNewInputVar().assumePositive()
                  val result = APAInputCombination(gcd_var).replaceList(input_assignments flatMap (_.extract))
                  assert(result.isPositiveZero)
                  addSingleInputAssignment(gcd_var, n_positive)
                  result
              }
              addSingleInputAssignment(x, APAInputDivision(const_part, gcd_expr).simplified)
              const_part = APAInputCombination(0, (1, x)::Nil)
              o1_coefs = o1_coefs map (APAInputDivision(_, gcd_expr).simplified)
            } else {
              var (cond1, prog1) = APASynthesis.solve(output_variables, APAEqualZero(pac.assumeAllCoefficientsAreZero) :: rest_equalities ++ non_equalities) // Case where the coefficients are null.
              cond1 = cond1.assumeBefore(coefs_are_zero)
              var (cond2, prog2) = APASynthesis.solve(output_variables, APAEqualZero(pac.assumeNotAllCoefficientsAreZero)  :: rest_equalities ++ non_equalities) //solve with the knowledge that not all the coefficients are null.
              cond2 = cond2.assumeBefore(APANegation(coefs_are_zero))
              return APACaseSplit.optimized((cond1, prog1)::(cond2, prog2)::Nil)
            }
        }
        // CONTINUE_POINT
        // Now the gcd of the output variables is for sure 1.
        // We find a solution to o1_coefs.o1_vars + 1 = 0
        // Then we know that by multiplying the first line by const_part, we obtain the general solution
        // Express the input variables by assignments

        val new_input_variables: List[List[InputVar]]= o1_vars.indices.toList map { _ => o1_vars.indices.toList map { _ => getNewInputVar()}}
        addBezoutInputAssignment(new_input_variables, o1_coefs)

        val first_line:List[APACombination] = new_input_variables.head map {
          case iv =>
            val p = APAInputCombination(0, (1, iv)::Nil)
            p.replaceList(input_assignments flatMap (_.extract)) match {
              case t@APAInputCombination(i, Nil) =>
                removeInputAssignment(iv)
                APACombination(const_part * t)
              case t@APAInputCombination(0, (i, v)::Nil) if Math.abs(i) == 1 => // Simple case 2
                removeInputAssignment(iv)
                APACombination(const_part * t)
              case _ => // If it's not an integer, keep the variable name.
                APACombination(const_part * p)
            }
        }
        // From this solution, we introduce |o1| - 1 new variables to solve the equality and remove the equation.
        val new_assignments:List[APACombination] = new_input_variables.tail.foldLeft(first_line:List[APACombination]) { case (assignments, line) =>
            val y = getNewOutputVar()
            (assignments zip line) map {
              case (expr:APACombination, iv) =>
                //expr + y*iv
                val p = APAInputCombination(0, (1, iv)::Nil)
                p.replaceList(input_assignments flatMap (_.extract)) match {
                  case t@APAInputCombination(i, Nil) =>  // Simple case 2
                    removeInputAssignment(iv)
                    expr + (APACombination(y)*t)
                  case t@APAInputCombination(0, (i, v)::Nil) if Math.abs(i) == 1 => // Simple case 2
                    removeInputAssignment(iv)
                    expr + (APACombination(y)*t)
                  case _ =>
                    expr + (APACombination(y)*p)
                }
            }
        }
        // We add the variables if they are needed.
        //if(((new_assignments flatMap (_.input_variables)).distinct intersect new_input_variables) != Nil)


        //var new_equalities = rest_equalities
        //var new_nonequalities = non_equalities
        val assignments = (o1_vars zip new_assignments)
        assignments foreach {
          case (v, pac) => addOutputAssignment(v, pac)
            //val (new_eqs1, new_noneqs1) = partitionPAEqualZero(new_equalities map (_.replace(v, pac)))
            //val (new_eqs2, new_noneqs2) = partitionPAEqualZero(new_nonequalities map (_.replace(v, pac)))
            //new_equalities = new_eqs1 ++ new_eqs2
            //new_nonequalities = new_noneqs1 ++ new_noneqs2
            delOutputVar(v)
        }
        //var new_remaining_disjunctions = remaining_disjunctions map (_.replaceList(assignments))
        val newfs = FormulaSplit(rest_equalities, non_equalities, remaining_disjunctions).replaceList(assignments)
        solveEqualities(newfs)
    }
  }

  def setRemainingVariablesToZero(output_variables : List[OutputVar]):Unit = output_variables match {
    case Nil =>
    case y::q =>
      output_variables_initial contains y match {
        case true => output_assignments = propagateAssignment(y, APACombination(APAInputCombination(0, Nil), Nil), output_assignments, output_variables_initial)
                     addOutputAssignment(y, APACombination(APAInputCombination(0, Nil), Nil))
                     delOutputVar(y)
                     setRemainingVariablesToZero(q)
        case false => output_assignments = propagateAssignment(y, APACombination(APAInputCombination(0, Nil), Nil), output_assignments, output_variables_initial)
                      delOutputVar(y)
                      setRemainingVariablesToZero(q)
      }
  }

  // Returns (cond, l_left, l_right, l_remaining) such that:
  // l_left contains elements  (A, a) such that A <= a*v
  // l_right contains elements (b, B) such that b*v <= B
  // l_remaining contains elements which do not contain v
  // l_cond is a list of formulas
  // Properties : The length of the stream is 3^l_formulas.size of the first element.
  def getInequalitiesForVariable(v: OutputVar, inequalities:List[APAGreaterEqZero]): Stream[(List[APAFormula], List[(APACombination, APAInputTerm)], List[(APAInputTerm, APACombination)], List[APAEquation])] = {
    def getInequalitiesForVariable_aux(v: OutputVar,
                                     inequalities:List[APAEquation],
                                     result:       (List[APAFormula], List[(APACombination, APAInputTerm)], List[(APAInputTerm, APACombination)], List[APAEquation])
                                    )   :   Stream[(List[APAFormula], List[(APACombination, APAInputTerm)], List[(APAInputTerm, APACombination)], List[APAEquation])] =
      inequalities match {
        case Nil =>
          // At this split point, we can solve.
          Stream(result)
      case ((p@APAGreaterEqZero(pac@APACombination(c, o)))::q) =>
        val (l_formulas, l_left, l_right, l_remaining)=result
        o find (_._2 == v) match {
          case None =>
              getInequalitiesForVariable_aux(v, q, (l_formulas, l_left, l_right, p::l_remaining))
          case Some(found_element@(k, v)) =>
            if(k.isPositive)
              getInequalitiesForVariable_aux(v, q, (l_formulas, (APACombination(c, o.filterNot(_ ==  found_element)) * (-1), k)::l_left, l_right, l_remaining))
            else if(k.isZero) // Should not happen, but this is just to keep a coherent skeleton.
              getInequalitiesForVariable_aux(v, q, (l_formulas, l_left, l_right, APAGreaterEqZero(APACombination(c, o.filterNot(_ ==  found_element)))::l_remaining))
            else if(k.isNegative)
              getInequalitiesForVariable_aux(v, q, (l_formulas, l_left, (-k, APACombination(c, o.filterNot(_ ==  found_element)))::l_right, l_remaining))
            else {
              def replaceLeftBound(left: List[(APACombination, APAInputTerm)], t1: APAInputTerm, s: SignAbstraction): List[(APACombination, APAInputTerm)] = {
                left map {
                  case (pac, i) =>
                    val result = (pac.assumeSignInputTerm(t1, s), i.assumeSignInputTerm(t1, s))
                    result
                }
              }
              def replaceRightBound(right: List[(APAInputTerm, APACombination)], t1: APAInputTerm, s: SignAbstraction): List[(APAInputTerm, APACombination)] = {
                right map {
                  case (i, pac) =>
                    val result = (i.assumeSignInputTerm(t1, s), pac.assumeSignInputTerm(t1, s))
                    result
                }
              }
              def replaceRemaining(remaining: List[APAEquation], t1: APAInputTerm, s: SignAbstraction): List[APAEquation] = {
                val result = remaining map (_.assumeSignInputTerm(t1, s))
                result
              }
              (if(k.can_be_positive) { // k can be positive
                val k_positive = k.assumeSign(1)
                assert(k_positive.isPositive)
                val new_l_formulas = (APACombination(k)   >  APAInputCombination(0))::l_formulas
                val new_l_left = (APACombination(c, o.filterNot(_ ==  found_element))*(-1), k_positive)::replaceLeftBound(l_left, k, k_positive)
                val new_l_right = replaceRightBound(l_right, k, k_positive)
                val new_l_remaining = replaceRemaining(l_remaining, k, k_positive)
                val new_q = replaceRemaining(q, k, k_positive)
                getInequalitiesForVariable_aux(v, new_q, (new_l_formulas, new_l_left, new_l_right, new_l_remaining))
              } else Stream()) append
              (if(k.can_be_zero) { // k can be zero
                val k_nul = APAInputCombination(0)
                assert(k_nul.isZero)
                val new_l_formulas = (APACombination(k) === APAInputCombination(0))::l_formulas
                val new_l_left = replaceLeftBound(l_left, k, k_nul)
                val new_l_right = replaceRightBound(l_right, k, k_nul)
                val new_l_remaining = APAGreaterEqZero(APACombination(c, o.filterNot(_ ==  found_element)))::replaceRemaining(l_remaining, k, k_nul)
                val new_q = replaceRemaining(q, k, k_nul)
                getInequalitiesForVariable_aux(v, new_q, (new_l_formulas, new_l_left, new_l_right, new_l_remaining))
              } else Stream()) append
              (if(k.can_be_negative) { // k can be negative
                val k_negative = k.assumeSign(-1)
                val mk_negative = -k_negative
                assert(mk_negative.isPositive)
                val new_l_formulas = (APACombination(k)  <  APAInputCombination(0))::l_formulas
                val new_l_left = replaceLeftBound(l_left, k, k_negative)
                val new_l_right = (mk_negative, APACombination(c, o.filterNot(_ ==  found_element)))::replaceRightBound(l_right, k, k_negative)
                val new_l_remaining = replaceRemaining(l_remaining, k, k_negative)
                val new_q = replaceRemaining(q, k, k_negative)
                getInequalitiesForVariable_aux(v, new_q, (new_l_formulas, new_l_left, new_l_right, new_l_remaining))
              } else Stream())
            }
        }
      case APATrue()::q =>
        val (l_formulas, l_left, l_right, l_remaining)=result
        getInequalitiesForVariable_aux(v, q, (l_formulas, l_left, l_right, l_remaining))
      case APAFalse()::q =>
        val (l_formulas, l_left, l_right, l_remaining)=result
        getInequalitiesForVariable_aux(v, q, (l_formulas, l_left, l_right, APAFalse()::l_remaining))
      case f::q =>
        throw new Error("Could not handle "+f)
    }
    getInequalitiesForVariable_aux(v, inequalities, (Nil, Nil, Nil, Nil))
  }

  /** Solve them, so now we only have non-equalities */
  /** The simplification of inequalities can generate new equalities, so we handle them. */
  def solveEquations(data: FormulaSplit):APASplit = {
    val FormulaSplit(equalities, non_equalities, remaining_disjunctions) = data
    // Let's extract the divisibility predicates and converts them to equalities.
    val (new_equalities, new_non_equalities) = partitionPAEqualZero(simplifyEquations(non_equalities))
    val total_equalities = equalities ++ new_equalities
    if(total_equalities != Nil) {
      solveEqualities(FormulaSplit(total_equalities, new_non_equalities, remaining_disjunctions))
    } else {
      val filtered_non_equalities = non_equalities filterNot (_==APATrue())
      if(filtered_non_equalities contains APAFalse()) return APAFalseSplit()
      //TODO :Here, verify that we don't have remaining_disjunctions anymore before handling the rest.
      if(!remaining_disjunctions.isEmpty) {
        assert(equalities == Nil)
        // We merge the current non equalities to the subproblems.
        val problems:Stream[FormulaSplit] = remaining_disjunctions map (FormulaSplit.conjunction(FormulaSplit(Nil, filtered_non_equalities, Stream.empty), _))
        // We recombine the subproblems together.
        val solutions = (problems map (APASynthesis.solveLazyEquations(input_variables, output_variables, _))).toList
        return APACaseSplit.optimized(solutions)
      }
      assert(remaining_disjunctions.isEmpty)

      /** Get only inequalities, plus maybe with "False" in other */
      val (equalities2, inequalities, is_consistent) = partitionPAGreaterEqZero(non_equalities)
      // equalities2 should be empty given that new_non_equalities cannot contain equalities
      assert(equalities2 == Nil)
      if(!is_consistent) return APAFalseSplit()

      /** Remove redundant inequalities, maybe generating equalities */
      //val (inequalities3, equalities3, is_consistent3) = removeRedundancies(inequalities)
      val (inequalities3, equalities3, is_consistent3) = (inequalities, Nil, true)

      if(!is_consistent3) return APAFalseSplit()
      if(equalities3 != Nil)
        return solveEqualities(FormulaSplit(equalities3, inequalities3, Stream.empty))

      var current_inequalities = inequalities3
      var current_noninequalities = List[APAEquation]()
      var is_consistent4 = true
      /** Solves for unbounded variables, when there are no case splits. */
      /** The value of output_variable is going to change, but we just need the initial one. */
      var current_inequalities_saved = APATrue()::current_inequalities
      while(current_inequalities != current_inequalities_saved) {
        current_inequalities_saved = current_inequalities
        output_variables foreach { y =>
          getInequalitiesForVariable(y, current_inequalities) match {
            case Stream((l_formula@Nil, l_left@Nil, l_right@Nil, l_remaining)) =>
              setRemainingVariablesToZero(y::Nil)
            case Stream((l_formula@Nil, l_left@Nil, l_right@l, l_remaining)) =>
              // Only bounded on the right by equations of style b*y <= pac, so we know that the integer upper bounds are pac/b
              val upper_bounds = l_right map { case (b , pac) => APADivision(pac, b).simplified }
              addOutputAssignment(y, APAMinimum(upper_bounds))
              delOutputVar(y)
              val (eqs, ineqs, consistency) = partitionPAGreaterEqZero(l_remaining)
              if(eqs != Nil) throw new Exception("Support for equalities appearing after split is not supported (yet)")
              is_consistent4 &&= consistency
              current_inequalities = ineqs
            case Stream((l_formula@Nil, l_left@l, l_right@Nil, l_remaining)) =>
              // Only bounded on the left by equations of style pac <= a*y, so we know that the integer upper bounds are (pac+a-1)/a
              val lower_bounds = l_left map { case (pac, a) => APADivision(pac + APACombination(a-APAInputCombination(1)), a).simplified }
              addOutputAssignment(y, APAMaximum(lower_bounds))
              delOutputVar(y)
              val (eqs, ineqs, consistency) = partitionPAGreaterEqZero(l_remaining)
              if(eqs != Nil) throw new Exception("Support for equalities appearing after split is not supported (yet)")
              current_inequalities = ineqs
              is_consistent4 &&= consistency
            case _ =>
          }
        }
      }
      if(!is_consistent4) return APAFalseSplit()
      if(output_variables == Nil) {
        addPrecondition(APAConjunction(current_inequalities))
        return APAEmptySplit()
      }

      // Now at this point, all variables are bounded on both sides.
      // Let's find the one for which the LCM of its coefficients is the smallest.
      // (Number of splits, min_coef)
      val output_variables_with_min_coefs:List[((Int, APAInputTerm), OutputVar)] = output_variables map {
        case y =>
          // Both l_left and r_right are not empty because of the previous computation
          getInequalitiesForVariable(y, current_inequalities) match {
            case Stream((l_formula, l_left, l_right, l_remaining)) =>
              assert(l_formula == Nil) // l_left and l_right only contain integers for bounds.
              val l_left_coefs:List[APAInputTerm] = l_left map (_._2)
              val l_right_coefs:List[APAInputTerm] = l_right map (_._1)
              val min_coef = APAInputLCM(l_left_coefs ++ l_right_coefs).simplified
              ((l_formula.size, min_coef), y)
            case Stream.cons((l_formula, l_left, l_right, l_remaining), _) =>
              // We have to split everything for this variable, so we don't do anything yet
              ((l_formula.size, APAInputCombination(0)), y)
          }
      }
      def min_coef(i1:((Int, APAInputTerm), OutputVar), i2:((Int, APAInputTerm), OutputVar)) : ((Int, APAInputTerm), OutputVar) = (i1, i2) match {
        case (t1@((split1, k1), v1), t2@((split2, k2), v2)) =>
          if(split1 < split2) t1 else (if(split1==split2) (if(needsLessOperations(k1, k2)) t1 else t2) else t2)
      }
      val (_, y) = output_variables_with_min_coefs.reduceRight(min_coef(_, _))

      getInequalitiesForVariable(y, current_inequalities) match {
        case Stream((Nil, l_left, l_right, l_remaining)) => // The signs are fully determined !!
          val (eqs, ineqs, consistency) = partitionPAGreaterEqZero(l_remaining)
          if(eqs != Nil) throw new Exception("Support for equalities appearing after split is not supported (yet)")
          current_inequalities = ineqs
          is_consistent4 &&= consistency

          if(l_right.size <= l_left.size) {
            val upper_bounds = l_right map { case (b , pac) => APADivision(pac, b).simplified }
            addOutputAssignment(y, APAMinimum(upper_bounds))
            delOutputVar(y)
          } else {
            val lower_bounds = l_left map { case (pac, a) => APADivision(pac + APACombination(a-APAInputCombination(1)), a).simplified }
            addOutputAssignment(y, APAMaximum(lower_bounds))
            delOutputVar(y)
          }
          val prog_needed_afterwards = output_variables != Nil

          // OptimizeMe : If a is smaller than b, use it instead of a.
          var output_variables_used = (output_variables_encountered).distinct
          var input_variables_used = (input_variables_encountered).distinct

          // We don't care about pairs of equations that are trivial to reduce.
          l_left foreach { case (eqA, a) =>
            l_right foreach { case (b, eqB) =>
              if(a==APAInputCombination(1, Nil)) current_inequalities = (APAGreaterEqZero(eqB-(eqA*b)))::current_inequalities
              else if(b==APAInputCombination(1, Nil)) current_inequalities = (APAGreaterEqZero((eqB*a)-eqA))::current_inequalities
            }
          }
          val l_left_filtered  = l_left  filterNot (_._2==APAInputCombination(1, Nil))
          val l_right_filtered = l_right filterNot (_._1==APAInputCombination(1, Nil))

          val lcm_value = APAInputLCM((l_left_filtered map (_._2)) ++ (l_right_filtered map (_._1))).simplified
          val lcm_int:Option[Int] = lcm_value match {
            case APAInputCombination(i, Nil) => Some(i)
            case _=> None
          }
          var lcm_expr = lcm_int match {
            case Some(i) => APAInputCombination(i)
            case None =>
              lcm_value match {
                case t@APAInputCombination(0, (i, v)::Nil) => t // Simple enough to get propagated easily
                case t => // "Too complicated"
                  val var_lcm = getNewInputVar()
                  addSingleInputAssignment(var_lcm, lcm_value)
                  APAInputCombination(var_lcm)
              }
          }

          val l_left_normalized = l_left_filtered map {
            case (eqA, a) =>
              assert(a.isPositive)
              eqA*(lcm_expr/a)
          }
          val l_right_normalized = l_right_filtered map {
            case (b, eqB) =>
              assert(b.isPositive)
              eqB*(lcm_expr/b)
          }

          var collected_new_input_variables:List[InputVar] = Nil
          val collected_new_equations:List[APAEquation] = l_right_normalized flatMap { case eqB =>
            val new_mod_bounds = l_left_normalized map { case eqA => (eqB - eqA) } filterNot {
              case APACombination(APAInputCombination(i, Nil), Nil) =>
                lcm_int match {
                  case Some(lcm) => i >= lcm-1
                  case None => false
                }
              case _ => false
            }
            // OptimizeMe ! If eqB%L contains only input variables, assign a new input variable to it.
            // OptimizeMe ! If eqB & eqA contain only input variables, add a precondition for it.
            new_mod_bounds match {
              case Nil => Nil // Ok, nothing to add
              case _ => // We need decomposition
                val k = getNewInputVar().assumePositiveZero()
                val ov = getNewOutputVar()
                collected_new_input_variables = k::collected_new_input_variables
                val k_expr = APAInputCombination(0, (1, k)::Nil)
                assert(k_expr.isPositiveZero)
                val new_ineqs = new_mod_bounds map {
                  case mod_bound =>
                    val result = APACombination(k_expr, Nil) <= mod_bound
                    result
                }
                val new_eq =   eqB === APACombination(k_expr, (lcm_value, ov)::Nil)
                new_eq::new_ineqs
            }
          }
          (collected_new_equations, collected_new_input_variables) match {
            case (Nil, Nil) =>
              if(current_inequalities == Nil) {
                APAEmptySplit()
              } else {
                solveEquations(FormulaSplit(Nil, current_inequalities, Stream.empty))
              }
            case (Nil, t) => throw new Error("How could this happen ? Both variables should be Nil, but the second one is "+t)
            case (t, Nil) => throw new Error("How could this happen ? Both variables should be Nil, but the first one is "+t)
            case (_,   _) =>
              val (condition, program) = APASynthesis.solve(collected_new_equations ++ current_inequalities)
              if(prog_needed_afterwards) {
                APAForSplit(collected_new_input_variables, APAInputCombination(0), lcm_value-APAInputCombination(1), condition, program)
              } else {
                //We don't need the program. Just the precondition
                APAForSplit(collected_new_input_variables, APAInputCombination(0), lcm_value-APAInputCombination(1), condition, APAProgram.empty)
              }
          }
        case stream => // The signs are not fully determined.
          // OptimizeMe ! Too bad, the split is already done, but we cannot continue that way
          // because we cannot assign it in other cases. Something better ?
          val possibilities = stream.toList
          val solutions = possibilities.zipWithIndex map {
            case (t@(l_formula, l_left, l_right, l_remaining), i) =>
              //println(i + " on variable " + y + " with equations " + t)
              val  left_equations = l_left  map {
                case (p, k) =>
                  if(k.isNotDefined) {
                    APAFalse()
                  } else {
                    assert(k.isPositive)
                    val right_member = APACombination(y)*k
                    p <= right_member
                  }
                }
              val right_equations = l_right map {
                case (k, p) =>
                  if(k.isNotDefined) {
                    APAFalse()
                  } else {
                    assert(k.isPositive)
                    val left_member = APACombination(y)*k
                    left_member <= p
                  }
              }
              val collected_new_equations = left_equations ++ right_equations ++ l_remaining
              //println("Collected : " + collected_new_equations)
              val (condition, program) = APASynthesis.solve(output_variables, collected_new_equations)
              val result = (condition && APAConjunction(l_formula), program)
              result
          }
          //println("Regrouping solutions")
          APACaseSplit.optimized(solutions)
      }
    }
  }


  def solve():(APACondition, APAProgram) = {
    /************* Main algorithm *************** */
    //***** Step 1: There are no quantifiers by construction. Nothing to do
    //***** Step 2: Remove divisibility constraints
    // Convert "Greater" to "GreaterEq"
    // Simplify everything
    //val equations2 = equations.simplified //simplifyEquations(equations)

    //***** Step 3 : converting to DNF : Nothing to do, the argument is a conjunction
    //***** Step 4 : Case Splitting. Nothing to do.
    //***** Step 5 : Removing equalities

    // All equations without output vars go directly to the global precondition
    //val (eq_with_outputvars, eq_without_outputvars) = equations2 partition (_.has_output_variables)
    //addPrecondition(APAConjunction(eq_without_outputvars))
    // Retrieve all equalities
    //var (equalities, non_equalities) = partitionPAEqualZero(eq_with_outputvars)

    val result = solveEquations(equations)

    // Looking for variables bounded only on one side.
    result match {
      case APAFalseSplit() =>
        setFalsePrecondition()
        (APACondition.optimized(Nil, APAConjunction(global_precondition), APAEmptySplitCondition()), APAProgram.empty)
      case (pa_split@APACaseSplit(list_cond_prog)) =>
        val splitted_conditions:List[APACondition] = list_cond_prog map (_._1)
        if(list_cond_prog == Nil) { // Nobody took care of the remaining output variables.
          setRemainingVariablesToZero(output_variables)
        }
        (APACondition.optimized(input_assignments, APAConjunction(global_precondition), APACaseSplitCondition(splitted_conditions)),
         APAProgram.optimized(input_variables_initial, input_assignments, pa_split, output_assignments, output_variables_initial))
      case pa_split@APAForSplit(vars, l, u, cond, prog) =>
        prog match {
          case t if t == APAProgram.empty =>
            (APACondition.optimized(input_assignments, APAConjunction(global_precondition), APAForCondition(vars, l, u, cond)),
             APAProgram.optimized(input_variables_initial, input_assignments, APAEmptySplit(), output_assignments, output_variables_initial))
          case _ =>
            (APACondition.optimized(input_assignments, APAConjunction(global_precondition), APAForCondition(vars, l, u, cond)),
             APAProgram.optimized(input_variables_initial, input_assignments, pa_split, output_assignments, output_variables_initial))
        }
      case pa_split@APAEmptySplit() =>
        setRemainingVariablesToZero(output_variables)
        (APACondition.optimized(input_assignments, APAConjunction(global_precondition), APAEmptySplitCondition()),
         APAProgram.optimized(input_variables_initial, input_assignments, pa_split, output_assignments, output_variables_initial))
      case t =>
        throw new Error("handling of "+t+" not implemented yet")
    }
  }
}
