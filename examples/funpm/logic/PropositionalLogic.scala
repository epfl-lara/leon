
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
  
package funpm.logic

sealed abstract case class IFormula()
case class IAnd(val left: IFormula, val right: IFormula) extends IFormula
case class IOr(val left: IFormula, val right: IFormula) extends IFormula
case class Neg(val f: IFormula) extends IFormula
case object Tru extends IFormula
case object Flse extends IFormula
case class IImply(val left: IFormula, val right: IFormula) extends IFormula


object Desugar {
  
  def apply(f: IFormula): IFormula = 
  /* postcondition res \in DesugaredFormula */
    f match {
      case Tru                => f
      case Flse               => f
      case IAnd(left,right)   => IAnd(apply(left),apply(right))
      case IOr(left,right)    => IOr(apply(left),apply(right))
      case Neg(f)             => Neg(apply(f))
      case IImply(left,right) => IOr(Neg(this.apply(left)),this.apply(right))
    }
  
  
  /**
    This examples is interesting because uses method desugarize postcondition
    in order to prove completeness of the PM.
  */
  def isDesugared(f: IFormula): Boolean = apply(f) match {
    case IAnd(left,right)   => isDesugared(left) && isDesugared(right)
    case IOr(left,right)    => isDesugared(left) && isDesugared(right)
    case Neg(f)             => isDesugared(f)
    case Tru                => true
    case Flse               => true
  }
    
  
}

object PropositionalLogic extends Application {
  // main
  assert(Desugar.isDesugared(Desugar.apply(IImply(IImply(Tru,Flse),Flse))))
}
