package leon.webDSL.webDescription
import leon.collection._
import leon.lang._
import leon.annotation._

/**
  * Created by dupriez on 3/11/16.
  *
  * All new subclasses of WebElement must also be registered in the pickler
  * (see shared/src/main/scala/shared/Picklers (the "webElementPickler" implicit val))
  */
sealed abstract class WebTree
sealed abstract class WebElement extends WebTree

@library
case class Element(tag: String, sons: leon.collection.List[WebElement], properties: leon.collection.List[WebAttribute], style: leon.collection.List[WebStyle]) extends WebElement {
  @isabelle.noBody()
  def attr(attributeName: String): Option[String] = {
    (properties.find { we => we.attributeName == attributeName }) map (_.attributeValue)
  }
  @isabelle.noBody()
  def apply(elems: List[WebTree]): Element = {
    val (sons2, properties2, style2) = leon.webDSL.webBuilding.implicits.extractElements(elems)
    Element(tag, sons ++ sons2, properties ++ properties2, style ++ style2) 
  }
  @ignore
  def apply(elems: WebTree*): Element = {
    var l: List[WebTree] = Nil[WebTree]()
    for (e <- elems) {
      l = Cons(e, l)
    }
    apply(l.reverse)
  }
}
case class TextElement(text: String) extends WebElement
case class WebAttribute(attributeName: String, attributeValue: String) extends WebTree
case class WebStyle(attributeName: String, attributeValue: String) extends WebTree 

case class WebElementWithID(we: WebElement, id: Int) extends WebElement
