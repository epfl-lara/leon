package funcheck

import funcheck.lib.Specs._

object PropositionalLogic {
  @generator
  sealed abstract class Formula
  case class Or(left: Formula, right: Formula) extends Formula
  case class Neg(f: Formula) extends Formula
  case class True() extends Formula
  case class False() extends Formula
  case class Imply(left: Formula,right: Formula) extends Formula


  def desugar(f: Formula): Formula = f match {
    case True()            => f
    case False()           => f
    case Or(left,right)    => Or(desugar(left),desugar(right))
    case Neg(f)            => Neg(desugar(f))
    case Imply(left,right) => Or(Neg(desugar(left)),desugar(right))
  }
  
  def isDesugared(f: Formula): Boolean = f match {
    case Or(left,right)    => isDesugared(left) && isDesugared(right)
    case Neg(f)            => isDesugared(f)
    case True()            => true
    case False()           => true
    case i: Imply          => false
  }
  
  //Type refinement: A desugarized formula does not contain an Imply node.
  forAll{f : Formula => isDesugared(f) ==> (desugar(f) == f) }
  
    
  def main(args: Array[String]) = {}
}

