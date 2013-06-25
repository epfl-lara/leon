import scala.collection.immutable.Set
import leon.Annotations._
import leon.Utils._

object Addresses {
  
  case class Address(a: Int, b: Int, priv: Boolean)
  
  sealed abstract class List
  case class Cons(a: Address, tail:List) extends List
  case object Nil extends List

  def setA(l: List) : Set[Address] = l match {
    case Nil => Set.empty[Address]
    case Cons(a, l1) => Set(a) ++ setA(l1)
  }
  
	def size(l: List) : Int = l match {
	  case Nil => 0
	  case Cons(head, tail) => 1 + size(tail)
	}
	
  def hasPrivate(l: List): Boolean = l match {
    case Nil => false
    case Cons(a, l1) =>
      if (a.priv) true
      else hasPrivate(l1)
  }

  case class AddressBook(business : List, pers : List)
  
  def size(ab: AddressBook): Int = size(ab.business) + size(ab.pers)
  
//  def makeAddressBook(l: List): AddressBook = (l match {
//    case Nil => AddressBook(Nil, Nil)
//    case Cons(a, l1) => {
//      val res = makeAddressBook(l1)
//      if (a.priv) AddressBook(res.business, Cons(a, res.pers))
//      else AddressBook(Cons(a, res.business), res.pers)
//    }
//  }) ensuring {
//    res =>
//	  size(res) == size(l) &&
//	  !hasPrivate(res.business) &&
//	  hasPrivate(res.pers)
//  }
  
//  def makeAddressBook(l: List): AddressBook = (l match {
//    case Nil => AddressBook(Nil, Nil)
//    case Cons(a, l1) => {
//      val res = makeAddressBook(l1)
//      if (a.priv) AddressBook(res.business, Cons(a, res.pers))
//      else AddressBook(Cons(a, res.business), res.pers)
//    }
//  }) ensuring {
//    res =>
//	  size(res) == size(l) &&
//	  (if (size(res.business) > 0) {
//	    !hasPrivate(res.business)
//	  } else true ) &&
//	  (if (size(res.pers) > 0) {
//	    hasPrivate(res.pers)
//	  } else true )
//  }
//  
//  def makeAddressBook(l: List): AddressBook = 
//		choose {
//    (res: AddressBook) =>
//		  size(res) == size(l) &&
//		  (if (size(res.business) > 0) {
//		    !hasPrivate(res.business)
//		  } else true ) &&
//		  (if (size(res.pers) > 0) {
//		    hasPrivate(res.pers)
//		  } else true )
//  }
  
  def makeAddressBook(l: List): AddressBook = 
		choose {
    (res: AddressBook) =>
		  size(res) == size(l) &&
		  hasPrivate(res.pers) && !hasPrivate(res.business)
  }
  
}
