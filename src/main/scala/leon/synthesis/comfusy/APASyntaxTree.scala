package leon.synthesis.comfusy

/*****************************
 *  Abstract syntax tree     *
 *****************************/

// dummy
object APASyntaxTree

/** Describes the concept of a variable. */
trait APAVariable

/** A class which can be converted to a linear combination. */
trait ConvertibleToCombination {

  /** Returns the corresponding linear combination equivalent to this expression. */
  implicit def toCombination():APACombination
}

/** Class representing an output variable, with some syntactic sugar. */
case class OutputVar(name: String) extends APAVariable with ConvertibleToCombination {
  def toCombination():APACombination = APACombination(this)

  /** Syntactic sugar */
  /** Returns the addition of this variable with a linear combination. */
  def +(pac : APACombination) = pac+APACombination(this)

  /** Returns the addition of this variable with an input variable. */
  def +(v : InputVar) = APAInputCombination(v)+APACombination(this)

  /** Returns the addition of this variable with another output variable. */
  def +(v : OutputVar) = APACombination(v)+APACombination(this)

  /** Returns the multiplication of this variable by an integer. */
  def *(i : Int) = APACombination(i, this)

  /** Returns the multiplication of this variable by an input variable. */
  def *(i : InputVar):APACombination = APACombination(APAInputCombination(0, Nil), (APAInputCombination(0, (1, i)::Nil), this)::Nil)
}

/** Abstract class describing an expression. Almost everything is an expression, except variables.
 *  Methods to convert or extract are regrouped here.
 */
abstract sealed class APAExpression {

  /** Returns the list of output variables this expression contains. */
  def output_variables:List[OutputVar] = this match {
    case APACombination(c, o) => o map (_._2)
    case APADivides(c, pac) => pac.output_variables
    case APAEqualZero(pac) => pac.output_variables
    case APAGreaterZero(pac) => pac.output_variables
    case APAGreaterEqZero(pac) => pac.output_variables
    case APATrue() => Nil
    case APAFalse() => Nil
    case APADivision(pac, n) => pac.output_variables
    case APADisjunction(l) => (l flatMap (_.output_variables)).distinct
    case APAConjunction(l) => (l flatMap (_.output_variables)).distinct
    case APAMinimum(l) => (l flatMap (_.output_variables)).distinct
    case APAMaximum(l) => (l flatMap (_.output_variables)).distinct
    case APANegation(e)=> e.output_variables
  }

  /** Returns the list of input variables this expression contains. */
  def input_variables:List[InputVar] = this match {
    case APACombination(c, o) => (c.input_variables ++ ((o map (_._1)) flatMap (_.input_variables))).distinct
    case APADivides(c, pac) => (pac.input_variables ++ c.input_variables).distinct
    case APAEqualZero(pac) => pac.input_variables
    case APAGreaterZero(pac) => pac.input_variables
    case APAGreaterEqZero(pac) => pac.input_variables
    case APATrue() => Nil
    case APAFalse() => Nil
    case APADivision(pac, c) => (pac.input_variables ++ c.input_variables).distinct
    case APADisjunction(l) => (l flatMap (_.input_variables)).distinct
    case APAConjunction(l) => (l flatMap (_.input_variables)).distinct
    case APAMinimum(l) => (l flatMap (_.input_variables)).distinct
    case APAMaximum(l) => (l flatMap (_.input_variables)).distinct
    case APANegation(e)=> e.input_variables
  }

  /** Returns a boolean indicating if the number of output variables is at least 1. */
  def has_output_variables: Boolean = (output_variables != Nil) //OptimizeMe!

  /** Returns a simplified version of this expression. */
  def simplified: APAExpression

  /** Returns a version of this expression where all occurences of y have been replaced by the linear combination t. */
  def replace(y: OutputVar, t: APACombination): APAExpression

  /** Returns a string representing this expression. */
  override def toString = toCommonString

  /** Returns a string representing this expression. Alias for toString. */
  def toCommonString: String = toStringGeneral(APASynthesis.rendering_mode)

  /** Returns a string representing this expression, depending on the rendering mode rm.*/
  def toStringGeneral(rm: RenderingMode) = this match {
    case APADivides(n, pac) =>
      val pac_s = pac.toNiceString
      if(APASynthesis.advanced_modulo && APASynthesis.rendering_mode != RenderingPython) {
        val string_pac = (if(((pac_s indexOf '-') >= 0) || ((pac_s indexOf '+') >= 0))
          "("+ pac_s + ")"
        else
          pac_s)
        val advanced_divisibility = rm.mod_function(string_pac, n.toString) + " == 0"
        advanced_divisibility
      } else {
        val basic_divisibility = (if(((pac_s indexOf '-') >= 0) || ((pac_s indexOf '+') >= 0))
          ("("+ pac_s + ") % " + n + " == 0")
        else
          (pac_s + " % " + n + " == 0"))
        val zero_divisibility = pac_s + " == 0"
        n match {
          case n if n.isZero =>
            zero_divisibility
          case n if n.isPositive =>
            basic_divisibility
          case _ =>
            "(("+n+"==0 "+rm.and_symbol+" "+zero_divisibility+") "+rm.or_symbol+" ("+n+"!=0 "+rm.and_symbol+" "+basic_divisibility+"))"
        }
      }
    case APAEqualZero(pac) => pac.toString + " == 0"
    case APAGreaterZero(pac) => pac.toString + " > 0"
    case APAGreaterEqZero(pac) => pac.toString + " >= 0"
    case APADivision(numerator, denominator) =>
      var string_numerator = numerator.toString
      var string_denominator = denominator.toString
      if((string_numerator indexOf '-') >=0  || (string_numerator indexOf '+') >=0)
        string_numerator = "("+string_numerator+")"
      if((string_denominator indexOf '-') >=0  || (string_denominator indexOf '+') >=0 || (string_denominator indexOf '*') >=0 || (string_denominator indexOf '/') >=0)
        string_denominator = "("+string_denominator+")"
      if(APASynthesis.rendering_mode == RenderingPython) // Python is cool : (-2)/3 = -1
        string_numerator+"/" + string_denominator
      else {
        numerator match {
          case APACombination(i, Nil) if i.isPositiveZero =>
            string_numerator+"/" + string_denominator
          case _ => "("+ string_numerator + " - " +  rm.mod_function(string_numerator, string_denominator) +")/" + string_denominator
        }
      }
    case APAMinimum(l) => rm.min_symbol + "(" + (l map (_.toString) reduceLeft(_ + ", " + _)) + ")"
    case APAMaximum(l) => rm.max_symbol + "(" + (l map (_.toString) reduceLeft(_ + ", " + _)) + ")"
    case pac@APACombination(_, _) => pac.toNiceString
    case APATrue() => rm.true_symbol
    case APAFalse() => rm.false_symbol
    case APAConjunction(eqs) => eqs match {
      case Nil => rm.true_symbol
      case (a::Nil) => a.toString
      case l => l map (_ match {
        case t if t.isInstanceOf[APAEquation] => t.toString
        case pac@APAConjunction(_) => pac.toString
        case t => "("+t.toString+")"
        }
      ) reduceLeft (_+ " "+rm.and_symbol+" " + _)
    }
    case APADisjunction(eqs) => eqs match {
      case Nil => rm.false_symbol
      case (a::Nil) => a.toString
      case l => l map (_ match {
        case t if t.isInstanceOf[APAEquation] => t.toString
        case pac@APADisjunction(_) => pac.toString
        case t => "("+t.toString+")"
        }
      ) reduceLeft (_+ " "+rm.or_symbol+" " + _)
    }
    case APANegation(eq) => rm.not_symbol+"("+eq.toString+")"
  }

  /** Returns a string representing this expression, in Scala. */
  def toScalaString = {
    toStringGeneral(RenderingScala)
  }

  /** Returns a string representing this expression, in Python. */
  def toPythonString = {
    toStringGeneral(RenderingPython)
  }

  /** Method to assume signs of input terms.
   *
   * To assume all occurences of the variable b to be >= 0 in myterm, call :
   *   myterm.assumeSignInputTerm(InputVar("b").toInputTerm, ASign(1, 1, 0))
   * To assume all occurences of the variable b to be <= 0 in myterm, call :
   *   myterm.assumeSignInputTerm(InputVar("b").toInputTerm, ASign(0, 1, 1))
  */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAExpression
}

/** Class representing formulas.
 *  A formula is an expression, which when evaluated, gives a boolean indicating if the formula is true or false.
 */
abstract sealed class APAFormula extends APAExpression {

  /** Returns a version of this formula where all occurences of the input variable y have been replaced by the input term t. */
  def replace(y: InputVar, t: APAInputTerm): APAFormula

  /** Returns a version of this formula where all occurences of the output variable y have been replaced by the linear combination t. */
  def replace(y: OutputVar, t: APACombination): APAFormula

  /** Processes multiple replacements of input variables. */
  def replaceListInput(lxt : List[(InputVar, APAInputTerm)]): APAFormula = {
    lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
  }

  /** Processes multiple replacements of output variables. */
  def replaceList(lxt : List[(OutputVar, APACombination)]): APAFormula = {
    lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
  }

  /** Returns a simplified version of this formula. */
  def simplified: APAFormula = this match {
    case APAConjunction(eqs) => val eqs_simplified = eqs map (_.simplified)
    eqs_simplified match {
      case Nil => APATrue()
      case l if l contains APAFalse() => APAFalse()
      case l => l filterNot (_ == APATrue()) match {
        case Nil => APATrue()
        case (a::Nil) => a
        case l => APAConjunction(l)
      }
    }
    case APADisjunction(eqs) => eqs map (_.simplified) match {
      case Nil => APAFalse()
      case l if l contains APATrue() => APATrue()
      case l =>  l filterNot (_ == APAFalse()) match {
        case Nil => APAFalse()
        case (a::Nil) => a
        case l => APADisjunction(l)
      }
    }
    case APANegation(f) => f.simplified match {
      case APATrue() => APAFalse()
      case APAFalse() => APATrue()
      case l => APANegation(l)
    }
    // This matching IS exhaustive since this method is overriden in other child classes.
    case t:APAFormula => throw new Error("formulas should have been simplified : "+this)
  }

  /** Returns the conjunction of this and that formulas. */
  def &&(that : APAFormula) = APAConjunction(this::that::Nil).simplified

  /** Returns the disjunction of this and that formulas. */
  def ||(that : APAFormula)  = APADisjunction(this::that::Nil).simplified

  /** Get a stream of the DNF form of the formula. */
  def getEquations = getEquations_tailrec(Nil)

  /** Get a stream of the DNF form of the formula. Recursive version. */
  def getEquations_tailrec(currentList: List[APAEquation]) : Stream[List[APAEquation]] = this match {
    case t@APADivides(_, _)     => Stream(currentList++List(t))
    case t@APAEqualZero(_)      => Stream(currentList++List(t))
    case t@APAGreaterZero(_)    => Stream(currentList++List(t))
    case t@APAGreaterEqZero(_)  => Stream(currentList++List(t))
    case APAConjunction(Nil)    => Stream(currentList)
    case APAConjunction(a::Nil) =>
      a.getEquations_tailrec(currentList)
    case APAConjunction(a::q)   =>
      val p1 = a.getEquations_tailrec(currentList)
      val p2 = APAConjunction(q).getEquations_tailrec(Nil)
      (p1, p2)
      val pp = (p1 map { eqs1 => p2 map { eqs2 => eqs1 ++ eqs2} })
      val result = pp.foldLeft(Stream.empty:Stream[List[APAEquation]])(_.append(_))
      result
    case APADisjunction(Nil)    => Stream(List(APAFalse()))
    case APADisjunction(a::Nil) => a.getEquations_tailrec(currentList)
    case APADisjunction(a::q) => a.getEquations_tailrec(currentList) append APADisjunction(q).getEquations_tailrec(currentList)
    case APATrue() => Stream(currentList)
    case APAFalse() => Stream(List(APAFalse()))
    case APANegation(f) => throw new Error("Negation is not supported yet")
  }

  /** Gets a stream of immediate equalities and inequalities if there are some + the rest as a stream. of possibilities. */
  def getLazyEquations = getLazyEquations_tailrec

  /** Gets a stream of immediate equalities and inequalities if there are some + the rest as a stream. of possibilities. Recursive version. */
  def getLazyEquations_tailrec: FormulaSplit = this match {
    case t@APADivides(_, _)     => FormulaSplit(Nil, List(t), Stream.empty)
    case t@APAEqualZero(_)      => FormulaSplit(t::Nil, Nil, Stream.empty)
    case t@APAGreaterZero(_)    => FormulaSplit(Nil, List(t), Stream.empty)
    case t@APAGreaterEqZero(_)  => FormulaSplit(Nil, List(t), Stream.empty)
    case APAConjunction(Nil)    => APATrue().getLazyEquations_tailrec
    case APAConjunction(a::Nil) =>        a.getLazyEquations_tailrec
    case APAConjunction(l)      => l map (_.getLazyEquations_tailrec) reduceLeft (FormulaSplit.conjunction(_,_))
    case APADisjunction(Nil)    => APAFalse().getLazyEquations_tailrec
    case APADisjunction(a::Nil) => a.getLazyEquations_tailrec
    case APADisjunction(l)      => FormulaSplit(Nil, Nil, l.toStream map (_.getLazyEquations_tailrec))
    case APATrue() => FormulaSplit(Nil, Nil, Stream.empty)
    case APAFalse() => FormulaSplit(Nil, APAFalse()::Nil, Stream.empty)
    case APANegation(f) => throw new Error("Negation is not supported yet")
  }

  /** Assumes the sign of the input term t1 throughout the formula. */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAFormula
}

/** Object providing methods for the class FormulaSplit.
 */
object FormulaSplit {

  /** Returns the conjunction of two FormulaSplit. */
  def conjunction(f1:FormulaSplit, f2:FormulaSplit):FormulaSplit = (f1, f2) match {
    case (FormulaSplit(eqs1, ineqs1, rest1), FormulaSplit(eqs2, ineqs2, rest2)) =>
        FormulaSplit(eqs1++eqs2, ineqs1++ineqs2, disjunction(rest1, rest2))
  }

  /** Returns the disjunction of two FormulaSplit. */
  def disjunction(sf1:Stream[FormulaSplit], sf2:Stream[FormulaSplit]):Stream[FormulaSplit] = {
    if(sf1.isEmpty) sf2
    else if(sf2.isEmpty) sf1
    else {
      sf1 flatMap { f1 => sf2 map { f2 => conjunction(f1, f2)}}
    }
  }
}

/** A FormulaSplit is a formula representing a conjunction of known equalities and inequalities, and a disjunction of other formula splits.
 *  e.g. FormulaSplit(eqs, noneqs, remaining) === (eqs && noneqs && (remaining1 || remaining2 || ...))
 */
case class FormulaSplit(eqs: List[APAEqualZero], noneqs : List[APAEquation], remaining:Stream[FormulaSplit]) {

  /** Replaces all output variables by corresponding value in this FormulaSplit. */
  def replaceList(assignments: List[(OutputVar, APACombination)]): FormulaSplit = {
    var new_equalities = eqs
    var new_nonequalities = noneqs
    assignments foreach {
      case (v, pac) =>
        val (new_eqs1, new_noneqs1) = APASynthesis.partitionPAEqualZero(new_equalities map (_.replace(v, pac)))
        val (new_eqs2, new_noneqs2) = APASynthesis.partitionPAEqualZero(new_nonequalities map (_.replace(v, pac)))
        new_equalities = new_eqs1 ++ new_eqs2
        new_nonequalities = new_noneqs1 ++ new_noneqs2
    }
    var new_remaining_disjunctions = remaining map (_.replaceList(assignments))
    FormulaSplit(new_equalities, new_nonequalities, new_remaining_disjunctions)
  }
}

/** Abstract class describing atomic equations, or literals, like divide predicates, greater or equal to zero predicates, equal to zero, etc.
 */
abstract sealed class APAEquation extends APAFormula {

  /** Returns a simplified version of this equation. */
  override def simplified: APAEquation = this match {
    case APADivides(_, APACombination(APAInputCombination(0, Nil), Nil)) => APATrue()
    case APADivides(APAInputCombination(1, Nil), pac) => APATrue()
    case APADivides(APAInputCombination(0, Nil), pac) => APAEqualZero(pac.simplified.normalizedForEquality)
    case APADivides(APAInputCombination(n, Nil), APACombination(APAInputCombination(i, Nil), Nil)) => if((i % n) == 0) APATrue() else APAFalse()
    case APADivides(n, pac) => APADivides(n, pac.simplified) // OptimizeMe ! divides by gcd of n and pac
    case APAEqualZero(pac) => APAEqualZero(pac.simplified.normalizedForEquality) match {
      case APAEqualZero(APACombination(n, Nil)) if n.isZero => APATrue()
      case APAEqualZero(APACombination(n, Nil)) if n.isNotZero => APAFalse()
      case t => t
    }
    case APAGreaterZero(pac) => APAGreaterZero(pac.simplified.normalized) match {
      case APAGreaterZero(APACombination(n, Nil)) if n.isPositive => APATrue()
      case APAGreaterZero(APACombination(n, Nil)) if n.isNotPositive => APAFalse()
      case t => t
    }
    case APAGreaterEqZero(pac) => APAGreaterEqZero(pac.simplified.normalized) match {
      case APAGreaterEqZero(APACombination(n, Nil)) if n.isPositiveZero =>
        APATrue()
      case APAGreaterEqZero(APACombination(n, Nil)) if n.isNotPositiveZero => APAFalse()
      case APAGreaterEqZero(tn@APACombination(n, Nil)) if n.isNegativeZero => APAEqualZero(tn)
      case t => t
    }
    case APATrue() => APATrue()
    case APAFalse() => APAFalse()
  }

  /** Returns a version of this equation where all occurences of the output variable y have been replaced by the term t. */
  def replace(y: OutputVar, t: APACombination): APAEquation

  /** Returns a version of this equation where each occurence of the input term t1 is assumed to have the sign s. */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation
}

/** Class representing terms, i.e. expressions that would evaluate to integers when fully evaluated.
 */
sealed abstract class APATerm extends APAExpression {

  /** Returns a version of this term where all occurences of the output variable y have been replaced by the term t. */
  def replace(y: OutputVar, t: APACombination):APATerm

  /** Returns a version of this term where all occurences of the input variable y have been replaced by the input term t. */
  def replace(y: InputVar, t: APAInputTerm):APATerm

  /** Returns a simplified version of this term. */
  def simplified:APATerm

  /** Processes multiple replacements of output variables. */
  def replaceList(lxt : List[(OutputVar, APACombination)]): APATerm = {
    lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
  }

  /** Processes multiple replacements of input variables. */
  def replaceListInput(lxt : List[(InputVar, APAInputTerm)]): APATerm = {
    lxt.foldLeft(this){ case (result, (x, t)) => result.replace(x, t) }
  }

  /** Returns a version of this term where each occurence of the input term t1 is assumed to have the sign s. */
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APATerm
}

/*******************
 *  General terms  *
 *******************/

/** Class representing a division of a linear combination by an input term.
 *  It is not required for the denominator to divide the expression.
 */ // TODO : comment from here.
case class APADivision(numerator : APACombination, denominator : APAInputTerm) extends APATerm {

  def replace(y: OutputVar, t: APACombination):APATerm = APADivision(numerator.replace(y, t), denominator).simplified

  def replace(y: InputVar, t: APAInputTerm):APATerm = APADivision(numerator.replace(y, t), denominator.replace(y, t)).simplified

  def simplified:APATerm = {
    val result = (numerator.simplified, denominator) match {
    case (n, APAInputCombination(1, Nil)) => n
    case (n, d0@APAInputCombination(0, Nil)) => APADivision(n, d0)
    case (APACombination(APAInputCombination(n, Nil), Nil), APAInputCombination(d, Nil)) =>
      APACombination(APAInputCombination((n - (d + (n % d))%d)/d, Nil), Nil)
    case (n, d) => APADivision(n, d)
    }
    result
  }


  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APATerm = {
    val new_numerator = numerator.assumeSignInputTerm(t1, s)
    val new_denominator = denominator.assumeSignInputTerm(t1, s)
    APADivision(new_numerator, new_denominator).simplified
  }
}

case class APAMinimum(expressions: List[APATerm]) extends APATerm {
  def replace(y: OutputVar, t: APACombination):APATerm = APAMinimum(expressions map (_.replace(y, t))).simplified
  def replace(y: InputVar, t: APAInputTerm):APATerm = APAMinimum(expressions map (_.replace(y, t))).simplified
  def simplified:APATerm = expressions match {
    case Nil => APACombination(0)
    case a::Nil => a.simplified
    case a::b::q =>
      (a.simplified, b.simplified) match {
        case (APACombination(APAInputCombination(i, Nil), Nil), APACombination(APAInputCombination(j, Nil), Nil)) => APAMinimum(APACombination(APAInputCombination(Math.min(i, j), Nil), Nil)::q).simplified //OptimizeMe
        case (p@APACombination(APAInputCombination(0, Nil), Nil), APACombination(j, Nil)) if j.isPositiveZero => APAMinimum(p::q).simplified //OptimizeMe
        case (APACombination(APAInputCombination(0, Nil), Nil), p@APACombination(j, Nil)) if j.isNegativeZero => APAMinimum(p::q).simplified //OptimizeMe
        case (a, b) => APAMinimum(a::b::(q map (_.simplified)))
      }
  }
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APATerm = {
    APAMinimum(expressions map (_.assumeSignInputTerm(t1, s))).simplified
  }
}
case class APAMaximum(expressions: List[APATerm]) extends APATerm {
  def replace(y: OutputVar, t: APACombination):APATerm = APAMaximum(expressions map (_.replace(y, t))).simplified
  def replace(y: InputVar, t: APAInputTerm):APATerm = APAMaximum(expressions map (_.replace(y, t))).simplified
  def simplified:APATerm = expressions match {
    case Nil => APACombination(0)
    case a::Nil => a.simplified
    case a::b::q =>
      (a.simplified, b.simplified) match {
        case (APACombination(APAInputCombination(i, Nil), Nil), APACombination(APAInputCombination(j, Nil), Nil)) => APAMaximum(APACombination(APAInputCombination(Math.max(i, j), Nil), Nil)::q).simplified //OptimizeMe
        case (APACombination(APAInputCombination(0, Nil), Nil), p@APACombination(j, Nil)) if j.isPositiveZero => APAMaximum(p::q).simplified //OptimizeMe
        case (p@APACombination(APAInputCombination(0, Nil), Nil), APACombination(j, Nil)) if j.isNegativeZero => APAMaximum(p::q).simplified //OptimizeMe
        case (a, b) => APAMaximum(a::b::(q map (_.simplified)))
      }
  }
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APATerm = {
    APAMaximum(expressions map (_.assumeSignInputTerm(t1, s))).simplified
  }
}

object APACombination {
  def apply(v: APAVariable):APACombination = this(1, v)
  def apply(k: Int, v: APAVariable):APACombination=  v match {
    case v@InputVar(n) => APACombination(APAInputCombination(0, (k, v)::Nil), Nil)
    case v@OutputVar(n) => APACombination(APAInputCombination(0, Nil), (APAInputCombination(k, Nil), v)::Nil)
  }
  def apply(i: Int): APACombination = APACombination(APAInputCombination(i, Nil), Nil)
  def apply(i: APAInputTerm): APACombination = APACombination(i, Nil)
  def apply(c: Int, i: List[(Int, InputVar)], o: List[(Int, OutputVar)]): APACombination = {
    APACombination(APAInputCombination(c, i), o map { case (i, v) => (APAInputCombination(i), v)})
  }
}

// Const_part does not contain any output variables
case class APACombination(const_part: APAInputTerm, output_linear: List[(APAInputTerm, OutputVar)]) extends APATerm with CoefficientAbstraction {
  if(output_linear == Nil) {
    setNoCoefficients()
  } else if(output_linear exists { case (i, _) if i.isNotZero => true; case _ => false}) {
    setNotAllCoefficientsAreZero()
  }
  def normalClone():this.type = APACombination(const_part, output_linear).asInstanceOf[this.type]
  // Sorting functions
  def by_OutputVar_name(i1:(APAInputTerm, OutputVar), i2:(APAInputTerm, OutputVar)) : Boolean = (i1, i2) match {
    case ((_, OutputVar(name1)), (_, OutputVar(name2))) => name1 < name2
  }
  // Regrouping functions
  def fold_Outputvar_name(i:(APAInputTerm, OutputVar), regrouped_vars:List[(APAInputTerm, OutputVar)]):List[(APAInputTerm, OutputVar)] = (i, regrouped_vars) match {
    case (i, Nil) => i::Nil
    case ((coef1, OutputVar(name1)), (coef2, OutputVar(name2))::q) if name1 == name2 => (coef1 + coef2, OutputVar(name1))::q
    case (i, q) => i::q
  }

  /** Simplified means that the variables are alphabetically sorted, that there are no null coefficients, and the gcd of all coefficients is 1. */
  def simplified: APACombination = {
    val output_linear2 = (output_linear sortWith by_OutputVar_name).foldRight[List[(APAInputTerm, OutputVar)]](Nil){ case (a, b) => fold_Outputvar_name(a, b)}
    APACombination(const_part.simplified, output_linear2 filterNot (_._1.isZero)).propagateCoefficientAbstraction(this)
  }

  // Normalized means that we are within an equality or inequality
  // It should have been simplified before (without 0-coefs)
  def normalized_aux(for_equality: Boolean): APACombination = {
    const_part match {
      case t:APAInputCombination if t.has_gcd_coefs =>
        var coefs:List[Int] = Nil
        ((output_linear forall {
          case (t@APAInputCombination(i, Nil), _) =>
            coefs = i::coefs
            true
          case _ => false
        }), output_linear.isEmpty) match {
          case (true, false) =>
            val gcd = Common.gcd(t.gcd_coefs, Common.gcdlist(coefs))
            (this/gcd).propagateCoefficientAbstraction(this)
          case (true, true) =>
            val gcd = t.gcd_coefs
            val factor = (if(for_equality) t.first_sign_present*gcd else gcd)
            (this/factor)
          case (false, _) => this
        }
      case _=> this
    }
  }
  def normalized = normalized_aux(false)
  def normalizedForEquality = normalized_aux(true)

  /** Division of this combination by an integer. Caution ! It should be divisible. */
  def /(i : Int): APACombination = {
    APACombination(const_part / APAInputCombination(i), output_linear map {t => (t._1 / APAInputCombination(i), t._2)})
  }
  /** Multiplication by an integer */
  def *(i : Int): APACombination = {
    val result = APACombination(const_part * APAInputCombination(i), output_linear map {t => (t._1 * APAInputCombination(i), t._2)})
    result.assumeMultCoefficientAbstraction(this, i)
  }
  /** Multiplication by an APAInputTerm */
  def *(i : APAInputTerm): APACombination = {
    APACombination(const_part * i, output_linear map {t => (t._1 * i, t._2)})
  }
  /** Addition between two combinations */
  def +(pac : APACombination): APACombination = pac match {
    case APACombination(c, o) =>
      val result = APACombination(const_part + c, output_linear ++ o).simplified
      result.assumeSumCoefficientAbstraction(this, pac)
  }
  /** Substraction between two combinations */
  def -(that : APACombination): APACombination = this + (that * (-1))
  /** Addition with a new variable and its coefficient */
  def +(kv : (APAInputTerm, OutputVar)): APACombination = this + APACombination(APAInputCombination(0, Nil), kv::Nil)
  def +(k : APAInputTerm): APACombination = this + APACombination(k, Nil)
  /** Substraction with a new variable and its coefficient */
  def -(kv : (APAInputTerm, OutputVar)): APACombination = this - APACombination(APAInputCombination(0, Nil), kv::Nil)
  def -(k : APAInputTerm): APACombination = this + APACombination(-k, Nil)
  def unary_-(): APACombination = (APACombination(APAInputCombination(0, Nil), Nil) - this)
  /** Comparison */
  def ===(that: APACombination):APAEquation = APAEqualZero(this - that).simplified
  def >= (that: APACombination):APAEquation = APAGreaterEqZero(this - that).simplified
  def >  (that: APACombination):APAEquation = APAGreaterZero(this - that).simplified
  def <= (that: APACombination):APAEquation = APAGreaterEqZero((-this) + that).simplified
  def <  (that: APACombination):APAEquation = APAGreaterZero((-this) + that).simplified
  def ===(that: APAInputTerm):APAEquation = this === APACombination(that)
  def >= (that: APAInputTerm):APAEquation = this >=  APACombination(that)
  def >  (that: APAInputTerm):APAEquation = this >   APACombination(that)
  def <= (that: APAInputTerm):APAEquation = this <=  APACombination(that)
  def <  (that: APAInputTerm):APAEquation = this <   APACombination(that)
  def divisible_by(that: APAInputTerm): APAEquation = APADivides(that, this)

  /** Replacement of a variable by another */
  def replace(y: OutputVar, t: APACombination):APACombination = (y, t) match {
    case (OutputVar(name), pac_for_y@APACombination(ci2, o2)) =>
      val (output_linear_with_y, output_linear_without_y) = output_linear partition (_._2 == y)
      val pac_without_y = APACombination(const_part, output_linear_without_y)
      val total_y_coefficient = (output_linear_with_y map (_._1)).foldLeft(APAInputCombination(0, Nil):APAInputTerm)(_+_)
      val result = pac_without_y + (pac_for_y*total_y_coefficient)
      result.simplified
  }
  def replace(y: InputVar, t: APAInputTerm):APACombination = {
    APACombination(const_part.replace(y, t), (output_linear map {case (k, v) => (k.replace(y, t), v)})).simplified
  }
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APACombination = {
    val new_const_part = const_part.assumeSignInputTerm(t1, s)
    val new_output_linear = output_linear map {case (i, v) => (i.assumeSignInputTerm(t1, s).propagateSign(i), v)}
    APACombination(new_const_part, new_output_linear).propagateCoefficientAbstraction(this)
  }

  def toNiceString:String = {
    def outputElementToString(kv : (APAInputTerm, OutputVar)) = kv._1 match {
      case APAInputCombination(1, Nil) => kv._2.name
      case APAInputCombination(-1, Nil) => "-" + kv._2.name
      case APAInputCombination(k, Nil) => k + "*" + kv._2.name
      case k => "("+ k.toString + ")*" + kv._2.name
    }
    def makePlus(l: List[String]):String = l match {
      case Nil => ""
      case a::p => val s = makePlus(p)
      if(s=="") a
      else if(a=="") s
      else if(s.charAt(0) == '-')
        a + s
      else
        a + "+" + s
    }
    var c_string = const_part.toString
    if(c_string == "0") c_string = ""
    var o_string = output_linear match {
      case Nil => ""
      case a::l => l.foldLeft(outputElementToString(a)) { (s, t2) =>
        val t2s = outputElementToString(t2)
        s + (if(t2s.charAt(0) =='-') t2s else "+" + t2s)}
    }
    val s = makePlus(c_string::o_string::Nil)
    if(s == "") "0" else s
  }
}

case class APADivides (coefficient: APAInputTerm, pac: APACombination) extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APADivides(coefficient, pac.replace(y, t)).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APADivides(coefficient.replace(y, t), pac.replace(y, t)).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APADivides(coefficient.assumeSignInputTerm(t1, s), pac.assumeSignInputTerm(t1, s)).simplified
}
case class APAEqualZero    (pac: APACombination) extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APAEqualZero(pac.replace(y, t)).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APAEqualZero(pac.replace(y, t)).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APAEqualZero(pac.assumeSignInputTerm(t1, s)).simplified
}
case class APAGreaterZero  (pac: APACombination) extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APAGreaterZero(pac.replace(y, t)).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APAGreaterZero(pac.replace(y, t)).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APAGreaterZero(pac.assumeSignInputTerm(t1, s)).simplified
}
case class APAGreaterEqZero(pac: APACombination) extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APAGreaterEqZero(pac.replace(y, t)).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APAGreaterEqZero(pac.replace(y, t)).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APAGreaterEqZero(pac.assumeSignInputTerm(t1, s)).simplified
}
case class APATrue() extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APATrue()
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APATrue()
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APATrue()
}
case class APAFalse() extends APAEquation {
  override def replace(y: OutputVar, t: APACombination): APAEquation = APAFalse()
  override def replace(y: InputVar,  t: APAInputTerm):   APAEquation = APAFalse()
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAEquation = APAFalse()
}

case class APAConjunction(eqs : List[APAFormula]) extends APAFormula {
  override def replace(y: OutputVar, t: APACombination): APAFormula = APAConjunction(eqs map (_.replace(y, t))).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAFormula = APAConjunction(eqs map (_.replace(y, t))).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAFormula =
    APAConjunction(eqs map (_.assumeSignInputTerm(t1, s))).simplified
}
case class APADisjunction(eqs : List[APAFormula]) extends APAFormula {
  override def replace(y: OutputVar, t: APACombination): APAFormula = APADisjunction(eqs map (_.replace(y, t))).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAFormula = APADisjunction(eqs map (_.replace(y, t))).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAFormula =
    APADisjunction(eqs map (_.assumeSignInputTerm(t1, s))).simplified
}
case class APANegation(eq: APAFormula) extends APAFormula {
  override def replace(y: OutputVar, t: APACombination): APAFormula = APANegation(eq.replace(y, t)).simplified
  override def replace(y: InputVar,  t: APAInputTerm):   APAFormula = APANegation(eq.replace(y, t)).simplified
  def assumeSignInputTerm(t1: APAInputTerm, s: SignAbstraction):APAFormula =
    APANegation(eq.assumeSignInputTerm(t1, s)).simplified
}
