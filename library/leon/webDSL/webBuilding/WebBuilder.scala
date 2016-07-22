package leon.webDSL.webBuilding
import leon.webDSL.webDescription._
import leon.collection._
import leon.annotation._
import scala.language.implicitConversions

@library
case class Acceptor[T](tag: String) {
  @isabelle.noBody() @library
  def :=(v: String) = WebAttribute(tag, v)
}

case class CssAcceptor[T](tag: String) {
  @isabelle.noBody() @library
  def :=(v: String) = WebStyle(tag, v)
}

@library
object implicits {
  @isabelle.noBody()
  implicit def toAttribute(e: String): WebTree = TextElement(e)
  
  /*def extractElements(e: List[WebTree], acc: List[WebElement], acc2: List[WebAttribute], acc3: List[WebStyle]): (List[WebElement], List[WebAttribute], List[WebStyle]) = e match {
    case Nil() => (acc.reverse, acc2.reverse, acc3.reverse)
    case Cons(e: WebElement, t) => extractElements(t, e::acc, acc2, acc3)
    case Cons(p: WebAttribute, t) => extractElements(t, acc, p::acc2, acc3)
    case Cons(p: WebStyle, t) => extractElements(t, acc, acc2, p::acc3)
  }*/
  @isabelle.noBody()
  def extractElements(e: List[WebTree]): (List[WebElement], List[WebAttribute], List[WebStyle]) = e match {
    case Nil() => (Nil(), Nil(), Nil())
    case Cons(e: WebElement, t) =>
      val abc = extractElements(t)
      (e::abc._1, abc._2, abc._3)
    case Cons(e: WebAttribute, t) => 
      val abc = extractElements(t)
      (abc._1, e::abc._2, abc._3)
    case Cons(e: WebStyle, t) => 
      val abc = extractElements(t)
      (abc._1, abc._2, e::abc._3)
  }
  @isabelle.noBody()
  def getStringProperty(tag: String, properties: List[WebAttribute], default: String): String = {
    properties.flatMap[String] { e => e match {
      case WebAttribute(tag2, e) if tag2 == tag=> e :: Nil[String]
      case _ => Nil()
    }}.headOption.getOrElse(default)
  }
  @isabelle.noBody()
  def getAllStringProperty(tag: String, properties: List[WebAttribute], default: String): String = {
    properties.foldLeft("") { (acc, e) => e match {
      case WebAttribute(tag2, e) if tag2 == tag => acc + e
      case _ => acc
    }}
  }
}

@library
object < {
  import implicits._
  @isabelle.noBody()
  def extract(tag: String, elems: List[WebTree]): Element = {
    val (children, properties, styles) = extractElements(elems)
    Element(tag, children, properties, styles)
  }
  
  val div = Element("div", Nil(), Nil(), Nil())
  val input = Element("input", Nil(), Nil(), Nil())
  val label = Element("label", Nil(), Nil(), Nil())
  val span = Element("span", Nil(), Nil(), Nil())
  val h1 = Element("h1", Nil(), Nil(), Nil())
  val h2 = Element("h2", Nil(), Nil(), Nil())
  val h3 = Element("h3", Nil(), Nil(), Nil())
  val h4 = Element("h4", Nil(), Nil(), Nil())
  val h5 = Element("h5", Nil(), Nil(), Nil())
  val h6 = Element("h6", Nil(), Nil(), Nil())
  val p = Element("p", Nil(), Nil(), Nil())
  val table = Element("table", Nil(), Nil(), Nil())
  val tbody = Element("tbody", Nil(), Nil(), Nil())
  val th = Element("th", Nil(), Nil(), Nil())
  val tr = Element("tr", Nil(), Nil(), Nil())
  val td = Element("td", Nil(), Nil(), Nil())
  val br = Element("br", Nil(), Nil(), Nil())
  val ul = Element("ul", Nil(), Nil(), Nil())
  val ol = Element("ol", Nil(), Nil(), Nil())
  val li = Element("li", Nil(), Nil(), Nil())
  val a = Element("a", Nil(), Nil(), Nil())
  val img = Element("img", Nil(), Nil(), Nil())
  
  val b = Element("b", Nil(), Nil(), Nil())
  val i = Element("i", Nil(), Nil(), Nil())
  val u = Element("u", Nil(), Nil(), Nil())
}

@library
object ^ {
  val name = Acceptor[String]("name")
  val tpe = Acceptor[String]("type")
  val value = Acceptor[String]("value")
  val placeholder = Acceptor[String]("placeholder")
  val id = Acceptor[String]("id")
  val className = Acceptor[String]("class")
  val classes = Acceptor[String]("class")
  val src = Acceptor[String]("src")
  val alt = Acceptor[String]("alt")
  val forid = Acceptor[String]("for")
  val cellpadding  = Acceptor[String]("cellpadding")
  val cellspacing  = Acceptor[String]("cellspacing")
  val colspan = Acceptor[String]("colSpan")
  val href = Acceptor[String]("href")
  val tabindex = Acceptor[String]("tabindex")
  val title = Acceptor[String]("title")
  val target = Acceptor[String]("target")
  val maxlength = Acceptor[String]("maxlength")
  
  val position = CssAcceptor[String]("position")
  val display = CssAcceptor[String]("display")
  
  val borderCollapse = CssAcceptor[String]("border-collapse")
  val textAlign = CssAcceptor[String]("text-align")
  val width = CssAcceptor[String]("width")
  val height = CssAcceptor[String]("height")
  val color = CssAcceptor[String]("color")
  val background = CssAcceptor[String]("background")
  val backgroundColor = CssAcceptor[String]("background-color")
  val backgroundImage = CssAcceptor[String]("background-image")
  
  val paddingRight = CssAcceptor[String]("padding-right")
  val paddingLeft = CssAcceptor[String]("padding-left")
  val paddingTop = CssAcceptor[String]("padding-top")
  val paddingBottom = CssAcceptor[String]("padding-bottom")
  val padding = CssAcceptor[String]("padding")
  
  val marginRight = CssAcceptor[String]("margin-right")
  val marginLeft = CssAcceptor[String]("margin-left")
  val marginTop = CssAcceptor[String]("margin-top")
  val marginBottom = CssAcceptor[String]("margin-bottom")
  val margin = CssAcceptor[String]("margin")
  
  val borderRight = CssAcceptor[String]("border-right")
  val borderLeft = CssAcceptor[String]("border-left")
  val borderTop = CssAcceptor[String]("border-top")
  val borderBottom = CssAcceptor[String]("border-bottom")
  val border = CssAcceptor[String]("border")
  val borderColor = CssAcceptor[String]("border-color")
  val borderRadius = CssAcceptor[String]("border-radius")
  
  val fontSize = CssAcceptor[String]("font-size")
  val lineHeight = CssAcceptor[String]("line-height")
  val fontWeight = CssAcceptor[String]("font-weight")
  val fontFamily = CssAcceptor[String]("font-family")
  
  val verticalAlign = CssAcceptor[String]("vertical-align")
  
  val top = CssAcceptor[String]("top")
  val bottom = CssAcceptor[String]("bottom")
  val left = CssAcceptor[String]("left")
  val right = CssAcceptor[String]("right")
  
  val minWidth = CssAcceptor[String]("min-width")
  val maxWidth = CssAcceptor[String]("max-width")  
  val minHeight = CssAcceptor[String]("min-height")
  val maxHeight = CssAcceptor[String]("max-height")
  
  val whiteSpace = CssAcceptor[String]("whiteSpace")
  val overflow = CssAcceptor[String]("overflow")
  
  def apply(name: String)  = Acceptor[String](name)
  
  def css(name: String) = CssAcceptor[String](name)
}
/*
object svg {
  object < {
    val path = Element("path", Nil(), Nil(), Nil())
  }
}*/