package webDSL

/**
  * Created by dupriez on 3/1/16.
  */
//TODO: Check if a WebPage is pickable by boopickle. I remember that boopickle can only pickle case classes, and inheritance of case classes is prohibited
sealed trait WebPage {
//  val content: List[WebElement] = List()
  val content: leon.collection.List[Int] = leon.collection.List()
  var testString = "Coucou"
}

case object ErrorWebPage extends WebPage {

}

case class BlankWebPage(sons: leon.collection.List[WebAttribute]) extends WebPage {
}
