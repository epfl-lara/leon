import leon._
import leon.annotation._
import leon.collection._
import leon.lang._

object Lists {

  @isabelle.script(
    name = "Safe_Head",
    source = """
      fun safe_head where
      "safe_head [] = None" |
      "safe_head (x # _) = Some x"

      lemma safe_head_eq_head[simp]:
        assumes "~ List.null xs"
        shows "safe_head xs = Some (hd xs)"
      using assms
      by (cases xs) auto
    """
  )
  @isabelle.function(term = "Safe_Head.safe_head")
  def safeHead[A](xs: List[A]): Option[A] = xs match {
    case Nil() => None()
    case Cons(x, _) => Some(x)
  }

  def lemma1[A](xs: List[A]) =
    (xs.isEmpty || safeHead(xs) == Some(xs.asInstanceOf[Cons[A]].h)).holds

  def lemma2[A](xs: List[A]) = {
    require(!xs.isEmpty)
    (xs.size > 0)
  }.holds

  def lemma3[A](xs: List[A], ys: List[A], zs: List[A]) =
    ((xs ++ ys) ++ zs == xs ++ (ys ++ zs)).holds

  def lemma4[A](xs: List[A], ys: List[A]) =
    ((xs ++ ys).content == (ys ++ xs).content).holds

  def lemma5[A](x: A, xs: List[A]) =
    ((x :: xs).content == xs.content ++ Set(x)).holds

  def lemma6[A](xs: List[A]) =
    (xs.reverse.reverse == xs).holds

  def lemma7[A, B](xs: List[A]) =
    (xs.zip(Nil[B]()) == Nil[(A, B)]()).holds

  def lemma7_check =
    (lemma7[Int, Int](Nil())).holds

  def lemma8[A](xs: List[A], x: A) =
    ((xs - x).content == xs.content -- Set(x)).holds

  def lemma9[A, B, C](xs: List[A], f: A => B, g: B => C) =
    (xs.map(f).map(g) == xs.map(x => g(f(x)))).holds

  @isabelle.function(term = "Fun.id")
  def identity[A](x: A) = x

  def lemma10[A](xs: List[A]) =
    (xs.map(identity) == xs).holds

  @isabelle.proof(method = """(induct "<var xs>", auto)""")
  def lemma11[A, B, C](xs: List[A], f: A => List[B], g: B => List[C]) =
    (xs.flatMap(f).flatMap(g) == xs.flatMap(x => f(x).flatMap(g))).holds

  def safeHead2[A](xs: List[A]): A = {
    require(xs.size > 0)
    xs.asInstanceOf[Cons[A]].h
  }

  def lemma12[A](xs: List[A]) =
    (xs.isEmpty || safeHead2(xs) == xs.asInstanceOf[Cons[A]].h).holds

  def lemma13[A](xs: List[A], x: A) =
    ((x :: xs).apply(0) == x).holds

  def lenTailrec[T](xs: List[T], n: BigInt): BigInt = xs match {
    case Nil() => n
    case Cons(_, xs) => lenTailrec(xs, 1 + n)
  }

  @isabelle.proof(method = """(induct "<var xs>" "<var n>" rule: [[leon_induct lenTailrec]], auto)""")
  def lemma14[A](xs: List[A], n: BigInt) =
    (lenTailrec(xs, n) >= n).holds

}
