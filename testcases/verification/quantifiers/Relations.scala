import leon.lang._
import leon.lang.synthesis._
import leon.proof._

object Relations {

  case class Relation[A](r: (A, A) => Boolean)

  def reflexive[A](rel: Relation[A]) = 
    forall( (x: A) => rel.r(x, x) )

  def symmetric[A](rel: Relation[A]) =
    forall( (x:A, y:A) => rel.r(x, y) == rel.r(y, x) )
  
  def antisymmetric[A](rel: Relation[A]) = 
    forall( (x:A, y:A) => ( rel.r(x,y) && rel.r(y,x) ) ==> (x == y) )
  
  def transitive[A](rel: Relation[A]) = 
    forall( (x:A, y:A, z:A) => ( rel.r(x,y) && rel.r(y,z) ) ==> rel.r(x,z) )
    
  def po[A](rel: Relation[A]) =
    reflexive(rel) &&
    antisymmetric(rel) &&
    transitive(rel)

}


object Proofs {
  import Relations._

  def int = {
    val rel = Relation[BigInt](_ <= _)
    po(rel) because {{
      po(rel)                                           ==| trivial |
      (
        reflexive(rel) &&
        antisymmetric(rel) &&
        transitive(rel)
      )                                                 ==| trivial |
      (
        forall( (x:BigInt) => 
          rel.r(x, x) 
        ) &&
        forall( (x:BigInt, y:BigInt) => 
          ( rel.r(x,y) && rel.r(y,x) ) ==> (x == y) 
        ) &&
        forall( (x:BigInt, y:BigInt, z:BigInt) => 
          ( rel.r(x,y) && rel.r(y,z) ) ==> rel.r(x,z) 
        )
      )                                                 ==| trivial |
      (
        forall( (x: BigInt) => 
          x <= x 
        ) &&
        forall( (x: BigInt, y:BigInt) => 
          ( x <= y && y <= x ) ==> ( x == y )
        ) &&
        forall( (x: BigInt, y: BigInt, z: BigInt) => 
          ( x <= y && y <= z ) ==> x <= z 
        )  
      )                                                 ==| trivial |
      true
    }.qed }
  }.holds

}

