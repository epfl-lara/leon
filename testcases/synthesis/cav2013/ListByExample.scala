import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Lists {
  sealed abstract class List
  case class Cons(head: Int, tail: List) extends List
  case class Nil() extends List

  def size(l:List): Int = (l match {
    case Nil() => 0
    case Cons(h,t) => 1 + size(t)
  }) ensuring(res => res >= 0)

  def listUp(a:Int,b:Int) : List = {
    require(a <= b)
    if (a == b) Cons(a,Nil())
    else Cons(a, listUp(a+1,b))
  } ensuring (res => size(res)==1+b-a)

  def listUp_syn(a:Int,b:Int) : List = {
    require(a <= b)
    choose((res:List) => 
    size(res)==1+b-a &&
    (!(a==5 && b==9) || res==Cons(5,Cons(6,Cons(7,Cons(8,Cons(9,Nil())))))) &&
    (!(a==100 && b==105) || 
      res==Cons(100,Cons(101,Cons(102,Cons(103,Cons(104,Cons(105,Nil())))))))
	 )
  }

  def listDown(a:Int,b:Int) : List = {
    require(a >= b)
    if (a == b) Cons(a,Nil())
    else Cons(a, listUp(a-1,b))
  } ensuring (res => size(res)==1+b-a)

  def listDown_syn(a:Int,b:Int) : List = {
    require(a >= b)
    choose((res:List) => 
    size(res)==1+b-a &&
    (!(a==9 && b==5) || res==Cons(9,Cons(8,Cons(7,Cons(6,Cons(5,Nil())))))) &&
    (!(a==105 && b==100) || 
      res==Cons(105,Cons(104,Cons(103,Cons(102,Cons(101,Cons(100,Nil())))))))
	 )
  }

  def concat_syn(a:List, b:List) : List = {
    choose((res:List) =>
      size(res) == size(a) + size(b) &&
      (!(a==listUp(1,5) && b==listUp(6,9)) || 
         res==listUp(1,9)) &&
      (!(a==listUp(101,105) && b==listUp(106,109)) || 
         res==listUp(101,109)) &&
      (!(a==listUp(201,205) && b==listUp(206,209)) || 
         res==listUp(201,209)) &&
      (!(a==listUp(301,304) && b==listUp(304,310)) || 
         res==listUp(301,310))
     )
  }

}
