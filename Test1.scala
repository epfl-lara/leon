import funcheck.lib.Specs._
import org.scalacheck.{Gen, Arbitrary}

object HeapTest {
  sealed abstract class Middle extends Top
  case class E()  extends Middle
  @generator sealed abstract class Top
  case class Elem(i: Int, j: Int) 

  @generator def create(): E = E()
  //@generator def create2(i: Int): Elem = Elem(i)

  def genE = Gen.value(E())
  def genE2 = Gen.value(E())

  @generator
  def genElemSynthetic(a: Int, b: Int) = Elem(a,b)

  def genElem = for {
    v2 <- Arbitrary.arbitrary[Int]
    v1 <- Arbitrary.arbitrary[Int]
  } yield Elem(v2,v2)

  implicit def arbE: Arbitrary[E] = Arbitrary(Gen.oneOf(genE,genE2))

  forAll[(Elem,Elem,Int)]( p => 1+1 == 2)
}