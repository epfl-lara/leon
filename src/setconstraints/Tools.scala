package setconstraints

import purescala.Definitions._

object Tools {

  def childOf(root: ClassTypeDef, classes: Seq[ClassTypeDef]) = classes.filter(_.parent == root)

  def toCaseClasses(classes: Seq[ClassTypeDef]): Seq[CaseClassDef] = 
    classes.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])

  def fix[A](f: (A) => A, a: A): A = {
    val res = f(a)
    if(res == a) a else fix(f, res)
  }

  def unzip3[A,B,C](seqs: Seq[(A,B,C)]): (Seq[A],Seq[B],Seq[C]) = 
    seqs.foldLeft((Seq[A](), Seq[B](), Seq[C]()))((a, t) => (t._1 +: a._1, t._2 +: a._2, t._3 +: a._3))

  def unzip3[A,B,C](sets: Set[(A,B,C)]): (Set[A],Set[B],Set[C]) = 
      sets.foldLeft((Set[A](), Set[B](), Set[C]()))((a, t) => (a._1 + t._1, a._2 + t._2, a._3 + t._3))

  def extract[A](p: (A) => Boolean, seq: Seq[A]): (Option[A], Seq[A]) = {
    val (s1, s2) = seq.partition(p)
    if(s1.isEmpty)
      (None, s2)
    else
      (Some(s1.head), s2 ++ s1.tail)
  }

  def extract[A](p: (A) => Boolean, set: Set[A]): (Option[A], Set[A]) = {
    val (s1, s2) = set.partition(p)
    if(s1.isEmpty)
      (None, s2)
    else
      (Some(s1.head), s2 ++ s1.tail)
  }
}
