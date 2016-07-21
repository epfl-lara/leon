import leon.lang._
import leon.annotation._
import leon.collection.List

object Friends { 

  case class Index[A : Mutable](i: Int) {
    def canIndex[B](arr: Array[B]): Boolean = {
      0 <= i && i < arr.length
    }
  }

  case class 
    Person(firstName: String, 
           lastName: String, 
           country: String,
           var friends: List[Index[Person]])

  case class Network(friends: Array[Person], var last: Int) {
    require(0 <= last && last < friends.length)
    
    def canExpand: Boolean = last + 1 < friends.length
    
    def befriend(me: Index[Person], newFriend: Index[Person]): Unit = {
      require(me.canIndex(friends) && newFriend.canIndex(friends))
      friends(me.i).friends = newFriend :: friends(me.i).friends
    }

    def signup(firstName: String, lastName: String, country: String): Unit = {
      require(canExpand)
      friends(last) = Person(firstName, lastName, country, List())
      last = last + 1
    }
    
  }

  def test(): Unit = {

    val network = Network(
      Array.fill(10)(Person("null", "null", "null", List())),
      0)

    network.signup("Regis", "Blanc", "CH")
    network.signup("Etienne", "Kneuss", "CH")
    network.befriend(Index(0), Index(1))
    assert(network.friends(0).friends.head == Index[Person](1))

  }

}
