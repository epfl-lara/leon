package funcheck.lib

object Specs {
  class generator extends StaticAnnotation

  /* more defs to come. */
  import org.scalacheck.{Arbitrary,Gen}
  import org.scalacheck.Prop
  import org.scalacheck.ConsoleReporter.testStatsEx
  import org.scalacheck.Test.check
  import org.scalacheck.Arbitrary.arbitrary
  
  implicit def extendedBoolean(b: Boolean) = new {
    def ==>(p: => Prop) = Specs.==>(b,p)
  }
  
  /** Implication */
  def ==>(b: => Boolean, p: => Prop): Prop = Prop ==> (b,p) 
  
  /** Converts a function into a universally quantified property */
  def forAll[A1,P](f: A1 => P): Prop = Prop.forAll(f)(null,null,null) 
    
  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,P] (
    f: (A1,A2) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,P] (
    f:  (A1,A2,A3) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,A4,P] (
    f:  (A1,A2,A3,A4) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3, _:A4)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,A4,A5,P] (
    f:  (A1,A2,A3,A4,A5) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3, _:A4, _:A5)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,A4,A5,A6,P] (
    f:  (A1,A2,A3,A4,A5,A6) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3, _:A4, _:A5, _:A6)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,A4,A5,A6,A7,P] (
    f:  (A1,A2,A3,A4,A5,A6,A7) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3, _:A4, _:A5, _:A6, _:A7)))

  /** Converts a function into a universally quantified property */
  def forAll[A1,A2,A3,A4,A5,A6,A7,A8,P] (
    f:  (A1,A2,A3,A4,A5,A6,A7,A8) => P
  ): Prop = forAll((a: A1) => forAll(f(a, _:A2, _:A3, _:A4, _:A5, _:A6, _:A7, _:A8)))
  
}
