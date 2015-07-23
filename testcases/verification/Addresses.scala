import leon.annotation._
import leon.lang._

object Addresses {
  // list of integers
  sealed abstract class List
  case class Cons(a: BigInt,b: BigInt,c: BigInt, tail:List) extends List
  case class Nil() extends List

  def setA(l:List) : Set[BigInt] = l match {
    case Nil() => Set.empty[BigInt]
    case Cons(a,b,c,l1) => Set(a) ++ setA(l1)
  }

  def containsA(x:BigInt,l:List) : Boolean = (l match {
    case Nil() => false
    case Cons(a,b,c,t) => a==x || containsA(x,t)
  }) ensuring (res => res == (setA(l) contains x))

  def theseAunique1(as:Set[BigInt],l:List) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 
      theseAunique1(as,l1) && !(as contains a) && (setA(l1) contains a)
  }

  def theseAunique2(as:Set[BigInt],l:List) : Boolean = (l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 
      theseAunique2(as,l1) && !(as contains a) && containsA(a,l1)
  }) ensuring (res => res==theseAunique1(as,l))

  def disjoint(x:Set[BigInt],y:Set[BigInt]):Boolean = {
    (x & y) == Set.empty[BigInt]
  }

  def uniqueAbsentAs(unique:Set[BigInt],absent:Set[BigInt],l:List) : Boolean = (l match {
    case Nil() => true
    case Cons(a,b,c,l1) => {
      !(absent contains a) &&
      (if (unique contains a) uniqueAbsentAs(unique -- Set(a), absent ++ Set(a), l1)
       else uniqueAbsentAs(unique, absent, l1))
    }
  }) ensuring (res => theseAunique1(unique,l) && disjoint(setA(l),absent))

  def allPos(l:List) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => 0 <= a && 0 <= b && 0 <= c && allPos(l1)
  }

  def allEq(l:List,k:BigInt) : Boolean = l match {
    case Nil() => true
    case Cons(a,b,c,l1) => c==k && allEq(l1,k)
  }

  def max(x:BigInt,y:BigInt) = if (x <= y) x else y

  def collectA(x:BigInt,l:List) : (BigInt,BigInt,List) = (l match {
    case Nil() => (BigInt(0),BigInt(0),Nil())
    case Cons(a,b,c,l1) if (a==x) => {
      val (b2,c2,l2) = collectA(x,l1)
      (max(b,b2),max(c,c2),l2)
    }
    case Cons(a,b,c,l1) if (a!=x) => {
      val (b2,c2,l2) = collectA(x,l1)
      (b2,c2,Cons(a,b,c,l2))
    }
  }) ensuring (res => {
    val (b,c,l1) = res
    !setA(l1).contains(x)
  })

/*
  def makeUniqueA(x:BigInt,l:List) : List = {
    require(allPos(l))
    val (b,c,l1) = collectA(x,l)
    Cons(x,b,c,l1)
  } ensuring(res => theseAunique1(Set(x),res))
*/

  case class AddressBook(business : List, pers : List)
  def isValidAB(ab:AddressBook) : Boolean = {
    allEq(ab.business,0) && allEq(ab.pers,1)
  }
  def setAB(l:List) : Set[(BigInt,BigInt)] = l match {
    case Nil() => Set.empty[(BigInt,BigInt)]
    case Cons(a,b,c,l1) => Set((a,b)) ++ setAB(l1)
  }

  def removeA(x:BigInt,l:List) : List = (l match {
    case Nil() => Nil()
    case Cons(a,b,c,l1) => 
      if (a==x) removeA(x,l1)
      else Cons(a,b,c,removeA(x,l1))
  }) ensuring(res => !(setA(res) contains x))

  def removeAg(x:BigInt,l:List,bg:BigInt) : List = (l match {
    case Nil() => Nil()
    case Cons(a,b,c,l1) => 
      if (a==x) removeAg(x,l1,bg)
      else Cons(a,b,c,removeAg(x,l1,bg))
  }) ensuring (res => !(setAB(res) contains (x,bg)))

  def removeA1(x:BigInt,l:List) : List = removeAg(x,l,0)

  @induct
  def removeAspec1(x:BigInt,l:List,bg:BigInt) : Boolean = {
    removeAg(x,l,bg) == removeA(x,l)
  } holds

  def removeAspec2(x:BigInt,l:List,k:BigInt) : Boolean = {
    require(allEq(l,k))
    allEq(removeA(x,l),k)
  } holds

  def updateABC(a:BigInt,b:BigInt,c:BigInt,l:List) : List = ({
    Cons(a,b,c,removeA(a,l))
  }) ensuring (res => setAB(res) contains (a,b))

  def lookupA(x:BigInt,l:List) : (BigInt,BigInt,BigInt) = {
    require(setA(l) contains x)
    l match {
      case Cons(a,b,c,l1) => {
	if (a==x) (a,b,c) 
	else lookupA(x,l1)
      }
    }
  } ensuring((res:(BigInt,BigInt,BigInt)) => {
    val (a,b,c) = res
    setAB(l) contains (a,b)
  })

  def makePers(ab:AddressBook, x:BigInt) : AddressBook = {
    require(isValidAB(ab) && (setA(ab.business) contains x))
    val (a,b,c) = lookupA(x,ab.business)
    val business1 = removeA(x, ab.business)
    // assert(allEq(business1,0))
    val pers1 = Cons(a,b,1,ab.pers)
    // assert(allEq(pers1,1))
    AddressBook(business1,pers1)
  } ensuring (res => isValidAB(res) && 
	      (setA(ab.pers) contains x) &&
	      !(setA(ab.business) contains x))

}
