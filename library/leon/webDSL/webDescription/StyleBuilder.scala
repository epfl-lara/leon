package leon.webDSL.webDescription

import leon.collection._
import leon.annotation._
import scala.Predef.String

@library
@isabelle.typ(name = "Leon_Types.style_builder")
@isabelle.constructor(name = "Leon_Types.style_builder.Style_Builder")
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