import leon.lang._

object Quantifiers {

  def swapping[A, B](p: (A, B) => Boolean) = {
    require(forall((x: A, y: B) => p(x, y)))
    forall((y: B, x: A) => p(x, y))
  }.holds

  def swapping_curry[A, B](p: A => B => Boolean) = {
    require(forall((x: A) => forall((y: B) => p(x)(y))))
    forall((y: B) => forall((x: A) => p(x)(y)))
  }.holds

  def inst[A](p: A => Boolean, a: A) = {
    require(forall((x: A) => p(a)))
    p(a)
  }.holds

  def exists[A](p: A => Boolean) =
    !forall((x: A) => !p(x))

  def drinkersPrinciple[A](d: A => Boolean) =
    exists((x: A) => d(x) ==> forall((y: A) => d(y))).holds

}
