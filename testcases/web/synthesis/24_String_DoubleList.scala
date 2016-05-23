import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object DoubleListRender {
  abstract class A
  case class B(i: AA, a: A) extends A
  case class N() extends A
  
  abstract class AA
  case class BB(i: A, a: AA) extends AA
  case class NN() extends AA
    
  // Two elements which do not contain each other but are in the same A should be the same.
  // Obviously wrong, but for the sake of displaying counter-examples.
  def lemma1(a: A, b: A, c: A): Boolean = {
    require(containsA_A(a, b) && containsA_A(a, c) && !containsA_A(b, c) && !containsA_A(c, b))
    b == c
  } holds

  def AtoString(a : A): String =  {
    ???[String] ask a
  }

  def AAtoString(a : AA): String =  {
    ???[String] ask a
  }
  
  def structurallyEqualA(a: A, b: A): Boolean = (a, b) match {
    case (N(), N()) => true
    case (B(i, k), B(j, l)) => structurallyEqualA(k, l) && structurallyEqualAA(i, j)
  }
  
  def structurallyEqualAA(a: AA, b: AA): Boolean = (a, b) match {
    case (NN(), NN()) => true
    case (BB(i, k), BB(j, l)) => structurallyEqualAA(k, l) && structurallyEqualA(i, j)
  }
  
  def containsA_A(a: A, b: A): Boolean = (a match {
    case N() => false
    case B(i, k) => containsAA_A(i, b) || containsA_A(k, b)
  })
  
  def containsAA_A(a: AA, b: A): Boolean = (a match {
    case NN() => false
    case BB(i, k) => i == b || containsA_A(i, b) || containsAA_A(k, b)
  })
  
  def containsA_AA(a: A, b: AA): Boolean = (a match {
    case N() => false
    case B(i, k) => i == b || containsAA_AA(i, b) || containsA_AA(k, b)
  })
  
  def containsAA_AA(a: AA, b: AA): Boolean = (a match {
    case NN() => false
    case BB(i, k) => containsA_AA(i, b) || containsAA_AA(k, b)
  })
}