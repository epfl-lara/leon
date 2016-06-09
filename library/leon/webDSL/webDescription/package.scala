package leon.webDSL
import leon.collection._
import leon.lang._
import leon.annotation._

package object webDescription {
  val Style = StyleSheet(Nil())
  
  @library
  case class StyleBuilder(name: String) {
    def :=(s: List[WebStyle]) = StyleRule(name, s)
    
    @ignore
    def :=(s: WebStyle*) = {
      var l: List[WebStyle] = Nil[WebStyle]()
      for (e <- s) {
        l = Cons(e, l)
      }
      StyleRule(name, l.reverse)
    }
  }
  
  implicit def toStyleBuilder(s: String): StyleBuilder = StyleBuilder(s)
}