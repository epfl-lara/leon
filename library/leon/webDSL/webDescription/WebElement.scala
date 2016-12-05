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
@isabelle.typ(name = "Leon_Types.web_tree")
sealed abstract class WebTree
sealed abstract class WebElement extends WebTree

@library
@isabelle.constructor(name = "Leon_Types.web_tree.Element")
case class Element(tag: String, sons: leon.collection.List[WebElement], properties: leon.collection.List[WebAttribute], style: leon.collection.List[WebStyle]) extends WebElement {
  @isabelle.noBody()
  def attr(attributeName: String): Option[String] = {
    (properties.find { we => we.attributeName == attributeName }) map (_.attributeValue)
  }
  def apply(elem: Option[WebTree]): Element = elem match {
    case None() => this
    case Some(e) => apply(List(e))
  }
  
  @isabelle.noBody()
  def apply(elems: List[WebTree]): Element = {
    val (sons2, properties2, style2) = leon.webDSL.webBuilding.implicits.extractElements(elems)
    Element(tag, sons ++ sons2, properties ++ properties2, style ++ style2) 
  }/* ensuring { (res: Element) =>
    res.tag == tag &&
    res.sons == sons ++ webElementsOf(l) &&
    res.properties == properties ++ propertiesOf(l) &&
    res.style == style ++ stylesOf(l)
  }*/
  @ignore
  def apply(elems: WebTree*): Element = {
    apply(varargToList(elems))
  }
}

@isabelle.constructor(name = "Leon_Types.web_tree.Text_Element")
case class TextElement(text: String) extends WebElement
@isabelle.constructor(name = "Leon_Types.web_tree.Web_Attribute")
case class WebAttribute(attributeName: String, attributeValue: String) extends WebTree
@isabelle.constructor(name = "Leon_Types.web_tree.Web_Style")
case class WebStyle(attributeName: String, attributeValue: String) extends WebTree 

@isabelle.constructor(name = "Leon_Types.web_tree.Web_Element_With_ID")
case class WebElementWithID(we: WebElement, id: Int) extends WebElement
