package purescala

object Common {
  import Trees.Variable
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

    def toVariable : Variable = Variable(this)

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

  trait ScalacPositional {
    self =>

    private var prow: Int = -1078
    private var pcol: Int = -1078

    def setPosInfo(row: Int, col: Int) : self.type = {
      prow = row
      pcol = col
      this
    }

    def setPosInfo(from: ScalacPositional) : self.type = { 
      val (or,oc) = from.posIntInfo
      prow = or
      pcol = oc
      this
    }

    def posIntInfo : (Int,Int) = (prow,pcol)

    def posInfo : String = if(prow != -1078) "(" + prow + "," + pcol + ")" else ""

    def <(other: ScalacPositional) : Boolean = {
      val (orow,ocol) = other.posIntInfo
      prow < orow || (prow == orow && pcol < ocol)
    }
  }
}
