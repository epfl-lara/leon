import leon.collection._
import leon.lang._

object Parser {
  def parse[T](s: String, fs: List[String => List[T]]): List[T] = {
    fs.flatMap(f => f(s))
  }
  
  def parseBefore(prefix: String, s: String): List[String] = {
    if(StrOps.startsWith(s, prefix)) List(StrOps.substring(s, StrOps.length(prefix), StrOps.length(s))) else Nil
  }
  
  def parseAfter(suffix: String, s: String): List[String] = {
    if(StrOps.endsWith(s, suffix)) List(StrOps.substring(s, 0, StrOps.length(s) - StrOps.length(suffix))) elseNil
  }
  
  def parseExact(res: String, s: String): Boolean = 
  
  def splitting(s: String): List[(String, String)] = {
    @tailrec def rec(i: Int, acc: List[(String, String)]): List[(String, String)] = {
	  if(i > StrOps.length(s)) {
	    acc
	  } else {
	    rec(i + 1, (StrOps.substring(s, 0, i), StrOps.substring(s, i, StrOps.length(s)))::acc)
	  }
	}
	rec(0, Nil)
  }
}
