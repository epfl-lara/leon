import leon.lang._
import leon.annotation._

/** A simple example of inductive proofs.
 * 
 * These require use of the @induct attribute. See SetIteration.scala for a
 * conceptually similar example where Leon cannot use inductive reasoning.
 */
object SimpleInduction {
  // a simple linked list
  abstract class SimpleList
  case class SimpleItem(v : Int, next : SimpleList) extends SimpleList
  case class SimpleEnd() extends SimpleList
  
  // true if all elements have value at least x
  def eltsAtLeast(list : SimpleList, x : Int) : Boolean =
    list match {
      case SimpleItem(v, next) => v >= x && eltsAtLeast(next, x)
      case SimpleEnd() => true
    }
  
  @induct
  def simpleProposition(list : SimpleList) : Boolean = {
    !eltsAtLeast(list, 5) || eltsAtLeast(list, 2)
  } holds
  
  @induct
  def noAction(list : SimpleList) : SimpleList = {
    require(eltsAtLeast(list, 5))
    list
  } ensuring (eltsAtLeast(list, 2))
  
  
  // A more explicit version of the above to more clearly illustrate where
  // inductive reasoning is required.
  
  // try to prove that x≥a → x≥b for each element
  def inductiveStep(list : SimpleList, a : Int, b : Int) : Boolean =
    list match {
      case SimpleItem(v, next) => (!(v >= a) || v >= b) && inductiveStep(next, a, b)
      case SimpleEnd() => true
    }
  
  // another encoding of simpleProposition
  @induct
  def inductiveProof(list : SimpleList) : Boolean = {
    inductiveStep(list, 5, 2)
  } holds
}
