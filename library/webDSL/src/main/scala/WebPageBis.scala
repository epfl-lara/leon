import leon.collection.List

/**
  * Created by dupriez on 3/1/16.
  */
//TODO: Check if a WebPage is pickable by boopickle. I remember that boopickle can only pickle case classes, and inheritance of case classes is prohibited
sealed trait WebPageBis {
//  val content: List[WebElement] = List()
  val content: leon.collection.List[Int] = List()
  var testString = "Coucou"
}

case object ErrorWebPageBis extends WebPageBis {

}

case class BlankWebPageBis(sons: List[WebAttributeBis]) extends WebPageBis {
}
