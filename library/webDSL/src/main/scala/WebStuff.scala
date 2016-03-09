/**
  * Created by dupriez on 3/4/16.
  */

sealed trait WebStuff

case class WebElement(attributes: leon.collection.List[WebAttribute], sons: leon.collection.List[WebElement]) extends WebStuff

sealed trait WebAttribute extends WebStuff

case class TestWebAttribute(oi: Int) extends WebAttribute

