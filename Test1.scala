import funcheck.lib.Specs
import funcheck.lib.Specs.generator
import org.scalacheck.{Gen, Arbitrary,Prop}

object HeapTest extends Application {
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

  Specs.forAll[(Int,Int)]( p => p._1 + p._2 == p._2 + p._1 )

  //Specs.forAll[Int]( p => p == p)
  Prop.forAll((a: Int,b: Int) => a+b == b+a)
  Prop.forAll((a: Int,b: Int, c: Int) => a+b+c == b+a+c)


  Prop.forAll((a: E) => a == a)
}