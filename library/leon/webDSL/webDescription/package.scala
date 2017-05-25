package leon.webDSL
import leon.collection._
import leon.annotation._
import scala.language.implicitConversions
import scala.Predef.String

package object webDescription {
  @library
  val Style = StyleSheet(Nil())
  
  implicit def toStyleBuilder(s: String): StyleBuilder = StyleBuilder(s)
}
