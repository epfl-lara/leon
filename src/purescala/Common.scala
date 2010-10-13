package purescala

object Common {
  import TypeTrees.Typed

  // the type is left blank (Untyped) for Identifiers that are not variables
  class Identifier private[Common](val name: String, val id: Int, alwaysShowUniqueID: Boolean = false) extends Typed {
    override def equals(other: Any): Boolean = {
      if(other == null || !other.isInstanceOf[Identifier])
        false
      else
        other.asInstanceOf[Identifier].id == this.id
    }

    override def hashCode: Int = id

    override def toString: String = {
      if(purescala.Settings.showIDs) {
        // angle brackets: name + "\u3008" + id + "\u3009"
        name + "[" + id + "]"
      } else if(alwaysShowUniqueID) {
        name + id
      } else {
        name
      }
    }

    def uniqueName : String = name + id

    private var _islb: Boolean = false
    def markAsLetBinder : Identifier = { _islb = true; this }
    def isLetBinder : Boolean = _islb
  }

  private object UniqueCounter {
    private var soFar: Int = -1

    def next: Int = {
      soFar = soFar + 1
      soFar
    }
  }

  object FreshIdentifier {
    def apply(name: String, alwaysShowUniqueID: Boolean = false) : Identifier = new Identifier(name, UniqueCounter.next, alwaysShowUniqueID)
  }
}
