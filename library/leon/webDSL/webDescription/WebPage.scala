package leon.webDSL.webDescription

import leon.annotation._
import leon.collection._
import leon.lang._

@isabelle.typ(name = "Leon_Types.style_rule")
@isabelle.constructor(name = "Leon_Types.style_rule.Style_Rule")
case class StyleRule(target: String, rules: List[WebStyle])

@library
@isabelle.typ(name = "Leon_Types.style_sheet")
@isabelle.constructor(name = "Leon_Types.style_sheet.Style_Sheet")
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

@isabelle.typ(name = "Leon_Types.web_page")
@isabelle.constructor(name = "Leon_Types.web_page.Web_Page")
case class WebPage(main: WebElement, css: StyleSheet)

@isabelle.typ(name = "Leon_Types.web_page_ided")
@isabelle.constructor(name = "Leon_Types.web_page_ided.Web_Page_IDed")
case class WebPageWithIDedWebElements(main: WebElementWithID, css: StyleSheet)
