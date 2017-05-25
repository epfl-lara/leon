package leon.synthesis.comfusy

/*****************************
 *  Expression abstractions  *
 *****************************/

// dummy
object APAAbstractions

/** This object provides methods for creating sign abstractions
 *  from integer arithmetic expressions of sign abstractions.
 *  Sign abstraction are typically applied to input terms.
 * 
 *  @author  Mikaël Mayer
 */
object SignAbstraction {

  /** Creates a sign abstraction from the sum of two sign abstractions.
   */
  def addSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    ASign((a.can_be_positive || b.can_be_positive), (a.can_be_zero && b.can_be_zero) || (a.can_be_positive && b.can_be_negative) || (b.can_be_positive && a.can_be_negative), (a.can_be_negative || b.can_be_negative))
  }
  
  /** Creates a sign abstraction from the sum of any number of sign abstractions.
   */
  def addSign(l: List[SignAbstraction]):ASign = {
    l.foldLeft(ASign(false, true, false))(addSign(_, _))
  }
  
  /** Creates a sign abstraction from the product of two sign abstractions.
   */
  def multSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    val result = ASign((a.can_be_positive && b.can_be_positive) || (a.can_be_negative && b.can_be_negative), (a.can_be_zero || b.can_be_zero), (a.can_be_positive && b.can_be_negative) || (a.can_be_negative && b.can_be_positive))
    result
  }
  
  /** Creates a sign abstraction from the product of any number of sign abstractions.
   */
  def multSign(l: List[SignAbstraction]):ASign = {
      l.foldLeft(ASign(true, false, false))(multSign(_, _))
  }
  
  /** Creates a sign abstraction from the division of sign abstractions.
   *  Raises an error if the divisor can be zero.
   */
  def divSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    if(b.can_be_zero)
      throw new Exception("Error : "+b+" can be zero")
    ASign((a.can_be_positive && b.can_be_positive) || (a.can_be_negative && b.can_be_negative), (a.can_be_positive || a.can_be_negative || a.can_be_zero) && (b.can_be_positive || b.can_be_negative || b.can_be_zero), (a.can_be_positive && b.can_be_negative) || (a.can_be_negative && b.can_be_positive))
  }
  
  /** Creates a sign abstraction from the opposite of a sign abstraction.
   */
  def oppSign(a: SignAbstraction):ASign = {
    ASign(a.can_be_negative, a.can_be_zero, a.can_be_positive)
  }
  
  /** Creates a sign abstraction from the absolute value of a sign abstraction.
   */
  def absSign(a: SignAbstraction):ASign = {
    ASign(a.can_be_negative || a.can_be_positive, a.can_be_zero, false)
  }
  
  /** Creates a sign abstraction from a number.
   */
  def number(i: Int):ASign = {
    ASign(i > 0, i == 0, i < 0)
  }
  
  /** Creates a sign abstraction from a linear combination of sign abstractions.
   *  i + l1*s1 + l2*s2 + l3*s3 ... + ln * sn
   *  
   *  @param i The constant coefficient of the linear combination
   *  @param l The list of pairs (l_i, s_i) where l_i is an integer and s_i a
   *           sign abstraction.
   */
  def linearCombinationSign(i: Int, l: List[(Int, SignAbstraction)]):ASign = {
    val l_sign = l map { case (i, sa) => multSign(number(i), sa)}
    addSign(number(i)::l_sign)
  }
  def mergeSign(a: SignAbstraction, b: SignAbstraction):ASign = {
    ASign(a.can_be_positive && b.can_be_positive, a.can_be_zero && b.can_be_zero, a.can_be_negative && b.can_be_negative)
  }
}

/** Class <code>SignAbstraction</code> represents a sign abstraction (>0, =0 and <0).
 *  Any class that extends it should implement the method <code>normalClone()</code>
 *  returning a clone from itself.
 *  The following methods are available:
 *  - Methods assume* (assumeZero, assumePositive...) to clone the expression with a more specialized abstraction 
 *  - Methods is* (isPositive, isNegativeZero) which check the sign abstraction capacities.
 *  - The method <codep>ropagateSign</code> can be overriden to propagate sign properties to sub-expressions.
 *
 *  @author  Mikaël Mayer
 */
trait SignAbstraction {
  
  //@{ Private section
  /** Private variables containing the abstraction. */
  private var private_pos: Boolean = true
  private var private_nul: Boolean = true
  private var private_neg: Boolean = true
  
  /** Clones the expression with a new abstraction. */
  private def cloneWithSign(a: SignAbstraction):this.type = {
    this.cloneWithSign(a.can_be_positive, a.can_be_zero, a.can_be_negative)
  }
  
  /** Clones the expression with a new abstraction where the signs are given. */
  private def cloneWithSign(pos_ : Boolean, nul_ : Boolean, neg_ : Boolean):this.type = {
    val result = normalClone().asInstanceOf[SignAbstraction]
    result.setSign(pos_, nul_, neg_)
    result.asInstanceOf[this.type]
  }
  //@}

  //@{ Protected section
  /** A direct method to set up the sign.
   * Used by subclasses methods only.*/
  protected def setSign(pos_ :Boolean, nul_ :Boolean, neg_ :Boolean):Unit = {
    private_pos = pos_
    private_nul = nul_
    private_neg = neg_
  }
  /** A direct method to set up the sign according to an integer.
   *  Used by subclasses methods only. */
  protected def setSign(i: Int):Unit = {
    setSign(i > 0, i == 0, i < 0) 
  }
  
  /** A direct method to set up the sign according to an existing abstraction.
   * Used by subclasses methods only. */
  protected def setSign(i: SignAbstraction):Unit = {
    setSign(i.can_be_positive, i.can_be_zero, i.can_be_negative)
  }
  
  /** Returns a clone of the expression updated with a better or new knowledge about the sign. */
  protected def propagateSign_internal(i: SignAbstraction):this.type = {
    cloneWithSign(can_be_positive && i.can_be_positive, can_be_zero && i.can_be_zero, can_be_negative && i.can_be_negative)
  }
  //@}

  //@{ Sign check methods
  /** Returns true if the expression can be positive. */
  def can_be_positive:Boolean = private_pos
  
  /** Returns true if the expression can be zero. */
  def can_be_zero:Boolean     = private_nul
  
  /** Returns true if the expression can be negative. */
  def can_be_negative:Boolean = private_neg
  
  /** Returns true if the expression is defined and positive. */
  def isPositive() = can_be_positive && !can_be_negative && !can_be_zero
  
  /** Returns true if the expression is defined and negative. */
  def isNegative() = !can_be_positive && can_be_negative && !can_be_zero
  
  /** Returns true if the expression is defined and (positive or zero). */ 
  def isPositiveZero() = (can_be_positive || can_be_zero) && !can_be_negative
    
  /** Returns true if the expression cannot be positive nor zero. */
  def isNotPositiveZero() = !can_be_positive && !can_be_zero
  
  /** Returns true if the expression is defined and (negative or zero). */
  def isNegativeZero() = (can_be_negative || can_be_zero) && !can_be_positive
  
  /** Returns true if the expression cannot be negative nor zero. */
  def isNotNegativeZero() = !can_be_negative && !can_be_zero
  
  /** Returns true if the expression cannot be positive. */
  def isNotPositive() = !can_be_positive
  
  /** Returns true if the expression cannot be negative. */
  def isNotNegative() = !can_be_negative
  
  /** Returns true if the expression is defined an is zero. */
  def isZero() = can_be_zero && !can_be_positive && !can_be_negative
  
  /** Returns true if the expression cannot be zero. */
  def isNotZero() = !can_be_zero
  
  /** Returns true if the expression is not defined. */
  def isNotDefined() = !can_be_positive && !can_be_negative && !can_be_zero
  //@}

  //@{ Assuming sign methods
  /** Assumes the sign of a integer. */
  def assumeSign(i: Int):this.type = {
    propagateSign(ASign(i > 0, i == 0, i < 0))
  }
  
  /** Assumes a sign == 0. */
  def assumeZero():this.type = {
    assumeSign(0)
  }
  
  /** Assumes a sign > 0 */
  def assumePositive():this.type = {
    assumeSign(1)
  }
  
  /** Assumes a sign < 0 */
  def assumeNegative():this.type = {
    assumeSign(-1)
  }
  
  /** Assumes a sign >= 0 */
  def assumePositiveZero():this.type = {
    propagateSign(ASign(true, true, false))
  }
  
  /** Assumes a sign <= 0 */
  def assumeNegativeZero():this.type = {
    propagateSign(ASign(false, true, true))
  }
  
  /** Assumes a sign != 0 */
  def assumeNotZero():this.type = {
    propagateSign(ASign(true, false, true))
  }
  
  /** Assumes a sign from a sign abstraction */
  def assumeSign(i: SignAbstraction):this.type = {
    propagateSign(ASign(i.can_be_positive, i.can_be_zero, i.can_be_negative))
  }
  
  /** Assumes a potential zero sign from a sign abstraction
   *  This is used products : a has the same zero-sign as a*b. */
  def assumeNotzerobility(i: SignAbstraction):this.type = {
    propagateSign(ASign(true, i.can_be_zero, true))
  }
  //@}
  
  //@{ Methods to specialize
  /** A cloning method to implement in order to use this class. */
  def normalClone():this.type
  
  /** A method which processes the sign propagation of an expression.
   *  Can be overriden to propagate the sign within sub-elements of the expression. */
  def propagateSign(i: SignAbstraction):this.type = {
    propagateSign_internal(i)
  }
  //@}
}


/** The simplest class to implement a sign abstraction. */
case class ASign(pos_ : Boolean, nul_ : Boolean, neg_ : Boolean) extends SignAbstraction {
  setSign(pos_, nul_, neg_)
  def normalClone():this.type = ASign(pos_, nul_, neg_).asInstanceOf[this.type]
}

/** The simplest class to implement a positive or zero sign abstraction. */
case class PositiveZeroSign() extends SignAbstraction {
  setSign(true, true, false)
  def normalClone():this.type = PositiveZeroSign().asInstanceOf[this.type]
}

/** Class <code>CoefficientAbstraction</code> represents an all-zero coefficients abstraction.
 *  The coefficients of a linear combination c_0 + c_1*y_1 + ... c_n*y_n are (c_1, ..., c_n)
 *  where the c_i are input terms and the y_i are output variables.
 *  Any class that extends <code>CoefficientAbstraction</code> should implement the method <code>normalClone()</code>
 *  returning a clone from itself.
 *  The following methods are available:
 *  - Methods assume* (assumeAllCoefficientsAreZero, ...) to clone the expression with a more specialized abstraction 
 *  - Checks Methods (allCoefficientsAreZero ...) which check the coefficient abstraction capacities.
 *
 *  @author  Mikaël Mayer
 */
trait CoefficientAbstraction {

  //@{ Private section
  /** Private variables containing the abstraction. */
  private var p_allCoefficientsCanBeZero:    Boolean = true
  private var p_oneCoefficientsCanBeNonZero: Boolean = true
  
  private def cloneWithCoefficientAbstraction(c: CoefficientAbstraction):this.type = {
    this.cloneWithCoefficientAbstraction(c.p_allCoefficientsCanBeZero, c.p_oneCoefficientsCanBeNonZero)
  }
  private def cloneWithCoefficientAbstraction(allCoefficientsCanBeZero_ : Boolean, oneCoefficientsCanBeNonZero_ : Boolean):this.type = {
    val result = normalClone().asInstanceOf[CoefficientAbstraction]
    result.setCoefficients(allCoefficientsCanBeZero_, oneCoefficientsCanBeNonZero_)
    result.asInstanceOf[this.type]
  }
  //@}
  
  //@{ Protected section
  /** A direct method to set up coefficient abstraction.
   *  Used by subclasses methods only. */
  protected def setNotAllCoefficientsAreZero() = {
    setCoefficients(false, true)
  }

  /** A direct method to set up coefficient abstraction.
   *  Used by subclasses methods only. */
  protected def setNoCoefficients() = {
    setCoefficients(true, true)
  }
  
  /** A direct method to set up coefficient abstraction.
   * Used by subclasses methods only. */
  protected def setCoefficients(a: Boolean, n: Boolean) = {
    p_allCoefficientsCanBeZero = a
    p_oneCoefficientsCanBeNonZero = n
  }
  
  /** A method to clone the expression with the knowledge of another coefficient abstraction. */
  protected def propagateCoefficientAbstraction(o : CoefficientAbstraction):this.type = {
    cloneWithCoefficientAbstraction(allCoefficientsCanBeZero    && o.allCoefficientsCanBeZero,
                                    oneCoefficientsCanBeNonZero &&  o.oneCoefficientsCanBeNonZero)
  }
  //@}
  
  //@{ Coefficient check methods
  /** Returns true if all the coefficients are zero. */
  def allCoefficientsAreZero    =  p_allCoefficientsCanBeZero && !p_oneCoefficientsCanBeNonZero
  
  /** Returns true if not all the coefficients are zero. */
  def notAllCoefficientsAreZero =  p_oneCoefficientsCanBeNonZero && !p_allCoefficientsCanBeZero
  
  /** Returns true if all the coefficients are zero. */
  def allCoefficientsCanBeZero    =  p_allCoefficientsCanBeZero
  
  /** Returns true if not all the coefficients are zero. */
  def oneCoefficientsCanBeNonZero =  p_oneCoefficientsCanBeNonZero
  //@}

  //@{ Assuming coefficients methods
  /** Assumes that all coefficients are zero. */
  def assumeAllCoefficientsAreZero : this.type = {
    propagateCoefficientAbstraction(ACoef(true, false))
  }
  
  /** Assumes that not all coefficients are zero. */
  def assumeNotAllCoefficientsAreZero : this.type = {
    cloneWithCoefficientAbstraction(ACoef(false, true))
  }
  
  /** Assumes a coefficient abstraction of a sum. */
  def assumeSumCoefficientAbstraction(a: CoefficientAbstraction, o: CoefficientAbstraction):this.type = {
    if(a.allCoefficientsAreZero && o.allCoefficientsAreZero) {
      assumeAllCoefficientsAreZero
    } else if(a.allCoefficientsAreZero) {
      propagateCoefficientAbstraction(o)
    } else if(o.allCoefficientsAreZero) {
      propagateCoefficientAbstraction(a)
    } else this
  }
  
  /** Assumes a coefficient abstraction of a multiplication by an integer. */
  def assumeMultCoefficientAbstraction(o: CoefficientAbstraction, i: Int):this.type = {
    if(i==0) {
      assumeAllCoefficientsAreZero
    } else {
      propagateCoefficientAbstraction(o)
    }
  }
  //@}

  
  //@{ Methods to specialize
  /** A cloning method to implement in order to use this class. */
  def normalClone():this.type
  //@}
}

/** The simplest class to implement a coefficient abstraction. */
case class ACoef(a: Boolean, n: Boolean) extends CoefficientAbstraction {
  setCoefficients(a, n)
  def normalClone():this.type = ACoef(a, n).asInstanceOf[this.type]
}