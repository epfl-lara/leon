package leon.webDSL.webDescription
/**
  * Created by dupriez on 3/1/16.
  */
import leon.annotation._
import leon.collection._
import leon.lang._

case class StyleRule(target: String, rules: List[WebStyle])

@library
case class StyleSheet(elems: List[StyleRule]) {
  @library
  def apply(l: List[StyleRule]): StyleSheet = {
    StyleSheet(elems ++ l)
  }
  @ignore
  def apply(newElems: StyleRule*): StyleSheet = {
    var l: List[StyleRule] = Nil[StyleRule]()
    for (e <- newElems) {
      l = Cons(e, l)
    }
    StyleSheet(elems ++ l.reverse)
  }
}

object WebPage {
  @library
  def apply(main: WebElement): WebPage = {
    WebPage(main, StyleSheet(Nil()))
  }
}

case class WebPage(main: WebElement, css: StyleSheet)

case class WebPageWithIDedWebElements(main: WebElementWithID, css: StyleSheet)

