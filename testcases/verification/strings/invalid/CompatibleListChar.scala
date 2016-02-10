import leon.lang._
import leon.annotation._
import leon.collection._
import leon.collection.ListOps._
import leon.lang.synthesis._

object CompatibleListChar {
  def rec[T](l : List[T], f : T => String): String = l match {
	case Cons(head, tail) => f(head) + rec(tail, f)
	case Nil() => ""
  }
  def customToString[T](l : List[T], p: List[Char], d: String, fd: String => String, fp: List[Char] => String, pf: String => List[Char], f : T => String): String =  rec(l, f) ensuring {
    (res : String) => (p == Nil[Char]() || d == "" || fd(d) == "" || fp(p) == "" || pf(d) == Nil[Char]()) && ((l, res) passes {
      case Cons(a, Nil()) => f(a)
    })
  }
  def customPatternMatching(s: String): Boolean = {
    s match {
	  case "" => true
	  case b => List(b) match {
	    case Cons("", Nil()) => true
	    case Cons(s, Nil()) => false // StrOps.length(s) < BigInt(2) // || (s == "\u0000") //+ "a"
		case Cons(_, Cons(_, Nil())) => true
		case _ => false
	  }
	  case _ => false
	}
  } holds
}