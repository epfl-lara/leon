import leon.annotation._
import leon.lang._
import leon.lang.synthesis._

object Addresses {
  // list of integers
  sealed abstract class List
  case class Cons(a:Int,b:Int,c:Int, tail:List) extends List
  case class Nil() extends List

  def setA(l:List) : Set[Int] = l match {
    case Nil() => Set.empty[Int]
    case Cons(a,b,c,l1) => Set(a) ++ setA(l1)
  }

  def allEq(l:List,k:Int) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => c==k && allEq(l1,k)
  }

  def containsA(x:Int,l:List) : Boolean = (l match {
    case Nil() => false
    case Cons(a,b,c,t) => a==x || containsA(x,t)
  }) ensuring (res => res == (setA(l) contains x))

  def containsA_syn(x:Int,l:List) : Boolean = choose((res:Boolean) =>
    res == (setA(l) contains x)
  )

  case class AddressBook(business : List, pers : List)
  def isValidAB(ab:AddressBook) : Boolean = {
    allEq(ab.business,0) && allEq(ab.pers,1)
  }
  def setAB(l:List) : Set[(Int,Int)] = l match {
    case Nil() => Set.empty[(Int,Int)]
    case Cons(a,b,c,l1) => Set((a,b)) ++ setAB(l1)
  }

  def removeA(x:Int,l:List) : List = (l match {
    case Nil() => Nil()
    case Cons(a,b,c,l1) => 
      if (a==x) removeA(x,l1)
      else Cons(a,b,c,removeA(x,l1))
  }) ensuring(res => !(setA(res) contains x))

  def lookupA(x:Int,l:List) : (Int,Int,Int) = {
    require(setA(l) contains x)
    l match {
      case Cons(a,b,c,l1) => {
	if (a==x) (a,b,c) 
	else lookupA(x,l1)
      }
    }
  } ensuring((res:(Int,Int,Int)) => {
    val (a,b,c) = res
    (a==x) && (setAB(l) contains (a,b))
  })

  def lookupA_syn(x:Int,l:List) : (Int,Int,Int) = {
    require(setA(l) contains x)
    choose((res:(Int,Int,Int)) => {
      val (a,b,c) = res
      (x == a) && (setAB(l) contains (a,b))
    })
  }

  def makePers(ab:AddressBook, x:Int) : AddressBook = {
    require(isValidAB(ab) && (setA(ab.business) contains x))
    val (a,b,c) = lookupA(x,ab.business)
    val business1 = removeA(x, ab.business)
    // assert(allEq(business1,0))
    val pers1 = Cons(a,b,1,ab.pers)
    // assert(allEq(pers1,1))
    AddressBook(business1,pers1)
  } ensuring (res => isValidAB(res) && 
	      (setA(res.pers) contains x) &&
	      !(setA(res.business) contains x))

  def makePers_syn(ab:AddressBook, x:Int) : AddressBook = {
    require(isValidAB(ab) && (setA(ab.business) contains x))
    choose((res:AddressBook) => isValidAB(res) && 
	   (setA(res.pers) contains x) &&
	   !(setA(res.business) contains x))
  }

}
