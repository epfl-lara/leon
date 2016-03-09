/**
  * Created by dupriez on 3/4/16.
  */

sealed trait WebStuffBis

case class WebElementBis(attributes: List[WebAttributeBis], sons: List[WebElementBis]) extends WebStuffBis

sealed trait WebAttributeBis extends WebStuffBis

case class TestWebAttributeBis(oi: Int) extends WebAttributeBis

