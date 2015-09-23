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

  def test = po(Relation[BigInt](_ <= _)).holds

}



