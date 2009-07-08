package plugin

import funcheck.lib.Specs._

object PropositionalLogic {
  
  

  // This crash because there are too many non-terminals, and the automatically 
  // injected generator may end up generating infinite formulas, which produce 
  // java.lang.StackOverflowError
  @generator
  sealed abstract class Formula
  case class And(left: Formula, right: Formula) extends Formula
  case class Or(left: Formula, right: Formula) extends Formula
  case class Neg(f: Formula) extends Formula
  case class True() extends Formula
  case class False() extends Formula
  case class Imply(left: Formula,right: Formula) extends Formula


 
  
  def desugar(f: Formula): Formula = f match {
    case True()            => f
    case False()           => f
    case And(left,right)   => And(desugar(left),desugar(right))
    case Or(left,right)    => Or(desugar(left),desugar(right))
    case Neg(f)            => Neg(desugar(f))
    case Imply(left,right) => Or(Neg(desugar(left)),desugar(right))
  }
  
  def isDesugared(f: Formula): Boolean = f match {
    case And(left,right)   => isDesugared(left) && isDesugared(right)
    case Or(left,right)    => isDesugared(left) && isDesugared(right)
    case Neg(f)            => isDesugared(f)
    case True()            => true
    case False()           => true
    case i: Imply          => false
  }
  
  forAll{f : Formula => isDesugared(f) ==> (desugar(f) == f) }
  // the above forAll invariant replaces the below somewhat cummbersome Matcheck spec
  /** Type refinement: A desugarized formula does not contain an Imply node.
                       This condition must hold recursively over the whole tree
  */
  /* constraint (\forall f. f \in DesugaredFormula <-->
                         ( f \in Tru |
                           f \in Flse |
                          (f \in Neg & Neg_getField_f(f) \in DesugaredFormula) |
                          (f \in IOr & IOr_getField_left(f) \in DesugaredFormula & IOr_getField_right(f) \in DesugaredFormula) |
                          (f \in IAnd & IAnd_getField_left(f) \in DesugaredFormula & IAnd_getField_right(f) \in DesugaredFormula)
                         )) 
  */
    
  def main(args: Array[String]) = 
    assert(isDesugared(desugar(Imply(Imply(True(),False()),False()))))
}

