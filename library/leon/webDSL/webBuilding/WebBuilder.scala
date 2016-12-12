package leon.webDSL.webBuilding
import leon.webDSL.webDescription._
import leon.collection._
import leon.annotation._
import scala.language.implicitConversions

@isabelle.typ(name = "Leon_Types.acceptor")
@isabelle.constructor(name = "Leon_Types.acceptor.Acceptor")
case class Acceptor[T](tag: String) {
  @library
  def :=(v: String) = WebAttribute(tag, v)
  @library
  def apply(v: String) = this := v
}

@isabelle.typ(name = "Leon_Types.css_acceptor")
@isabelle.constructor(name = "Leon_Types.css_acceptor.CSS_Acceptor")
case class CssAcceptor[T](tag: String) {
  @library
  def :=(v: String) = WebStyle(tag, v)
  @library
  def apply(v: String) = this := v
}

@isabelle.typ(name = "Leon_Types.element_decision")
@isabelle.constructor(name = "Leon_Types.element_decision.Element_Decision")
case class ElementDecision(b: Boolean) {
  @library
  def ?=(v: Element) = if(b) v else Element("", Nil(), Nil(), Nil())
}

@library
object implicits {
  implicit def toAttribute(e: String): WebTree = TextElement(e)
  
  implicit def toDecision(b: Boolean): ElementDecision = ElementDecision(b)
  
  /*def extractElements(e: List[WebTree], acc: List[WebElement], acc2: List[WebAttribute], acc3: List[WebStyle]): (List[WebElement], List[WebAttribute], List[WebStyle]) = e match {
    case Nil() => (acc.reverse, acc2.reverse, acc3.reverse)
    case Cons(e: WebElement, t) => extractElements(t, e::acc, acc2, acc3)
    case Cons(p: WebAttribute, t) => extractElements(t, acc, p::acc2, acc3)
    case Cons(p: WebStyle, t) => extractElements(t, acc, acc2, p::acc3)
  }*/
  @isabelle.noBody()
  def extractElements(e: List[WebTree]): (List[WebElement], List[WebAttribute], List[WebStyle]) = e match {
    case Nil() => (Nil(), Nil(), Nil())
    case Cons(e: Element, t) =>
      val abc = extractElements(t)
      if(e.tag != "") {
        if(e.tag == "#expand") {
          (e.sons ++ abc._1, e.properties ++ abc._2, e.style ++ abc._3)
        } else {
          (e::abc._1, abc._2, abc._3)
        }
      } else {
        abc
      }
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
  
  @isabelle.noBody()
  implicit def listWebElementToWebTree(l: List[Element]): List[WebTree] = l match {
    case Nil() => Nil()
    case Cons(x, xs) => Cons(x, xs)
  }
  
  def listElementToListWebElement(l: List[Element]): List[WebElement] = l match {
    case Nil() => Nil()
    case Cons(x, xs) => Cons(x, listElementToListWebElement(xs))
  }
  
  implicit def listWebTreeToWebTree(l: List[WebTree]): WebTree = {
    val abc = extractElements(l)
    Element("#expand", abc._1, abc._2, abc._3)
  }
  implicit def listWebElementToWebTree(l: List[WebElement]): WebTree = {
    Element("#expand", l, Nil(), Nil())
  }
  implicit def listElementToWebTree(l: List[Element]): WebTree = {
    Element("#expand", listElementToListWebElement(l), Nil(), Nil())
  }
  implicit def listWebAttributesToWebTree(l: List[WebAttribute]): WebTree = {
    Element("#expand", Nil(), l, Nil())
  }
  implicit def listWebStylesToWebTree(l: List[WebStyle]): WebTree = {
    Element("#expand", Nil(), Nil(), l)
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
  
  @isabelle.noBody()
  def apply(tagname: String): Element = Element(tagname, Nil(), Nil(), Nil())
  
  val a = apply("a")
  val abbr = apply("abbr")
  val acronym = apply("acronym")
  val address = apply("address")
  val applet = apply("applet")
  val area = apply("area")
  val article = apply("article")
  val aside = apply("aside")
  val audio = apply("audio")
  val b = apply("b")
  val base = apply("base")
  val basefont = apply("basefont")
  val bdi = apply("bdi")
  val bdo = apply("bdo")
  val big = apply("big")
  val blockquote = apply("blockquote")
  val body = apply("body")
  val br = apply("br")
  val button = apply("button")
  val canvas = apply("canvas")
  val caption = apply("caption")
  val center = apply("center")
  val cite = apply("cite")
  val code = apply("code")
  val col = apply("col")
  val colgroup = apply("colgroup")
  val command = apply("command")
  val datalist = apply("datalist")
  val dd = apply("dd")
  val del = apply("del")
  val details = apply("details")
  val dfn = apply("dfn")
  val dir = apply("dir")
  val div = apply("div")
  val dl = apply("dl")
  val dt = apply("dt")
  val em = apply("em")
  val embed = apply("embed")
  val fieldset = apply("fieldset")
  val figcaption = apply("figcaption")
  val figure = apply("figure")
  val font = apply("font")
  val footer = apply("footer")
  val form = apply("form")
  val frame = apply("frame")
  val frameset = apply("frameset")
  val h1 = apply("h1")
  val h2 = apply("h2")
  val h3 = apply("h3")
  val h4 = apply("h4")
  val h5 = apply("h5")
  val h6 = apply("h6")
  val head = apply("head")
  val header = apply("header")
  val hgroup = apply("hgroup")
  val hr = apply("hr")
  val html = apply("html")
  val i = apply("i")
  val iframe = apply("iframe")
  val img = apply("img")
  val input = apply("input")
  val ins = apply("ins")
  val kbd = apply("kbd")
  val keygen = apply("keygen")
  val label = apply("label")
  val legend = apply("legend")
  val li = apply("li")
  val link = apply("link")
  val map = apply("map")
  val mark = apply("mark")
  val menu = apply("menu")
  val meta = apply("meta")
  val meter = apply("meter")
  val nav = apply("nav")
  val noframes = apply("noframes")
  val noscript = apply("noscript")
  val `object` = apply("object")
  val ol = apply("ol")
  val optgroup = apply("optgroup")
  val option = apply("option")
  val output = apply("output")
  val p = apply("p")
  val param = apply("param")
  val pre = apply("pre")
  val progress = apply("progress")
  val q = apply("q")
  val rp = apply("rp")
  val rt = apply("rt")
  val ruby = apply("ruby")
  val s = apply("s")
  val samp = apply("samp")
  val script = apply("script")
  val section = apply("section")
  val select = apply("select")
  val small = apply("small")
  val source = apply("source")
  val span = apply("span")
  val strike = apply("strike")
  val strong = apply("strong")
  val style = apply("style")
  val sub = apply("sub")
  val summary = apply("summary")
  val sup = apply("sup")
  val table = apply("table")
  val tbody = apply("tbody")
  val td = apply("td")
  val textarea = apply("textarea")
  val tfoot = apply("tfoot")
  val th = apply("th")
  val thead = apply("thead")
  val time = apply("time")
  val title = apply("title")
  val tr = apply("tr")
  val track = apply("track")
  val tt = apply("tt")
  val u = apply("u")
  val ul = apply("ul")
  val `var` = apply("var")
  val video = apply("video")
  val wbr = apply("wbr")
}

@library
object ^ {
  @isabelle.noBody()
  def apply(name: String)  = Acceptor[String](name)
  
  @isabelle.noBody()
  def css(name: String) = CssAcceptor[String](name)
  
  val name = apply("name")
  val tpe = apply("type")
  val value = apply("value")
  val placeholder = apply("placeholder")
  val id = apply("id")
  val className = apply("class")
  val classes = apply("class")
  val src = apply("src")
  val alt = apply("alt")
  val forid = apply("for")
  val cellpadding  = apply("cellpadding")
  val cellspacing  = apply("cellspacing")
  val colspan = apply("colSpan")
  val href = apply("href")
  val tabindex = apply("tabindex")
  val title = apply("title")
  val target = apply("target")
  val maxlength = apply("maxlength")
  
  val position = css("position")
  val display = css("display")
  
  val borderSpacing = css("border-spacing")
  val borderCollapse = css("border-collapse")
  val textAlign = css("text-align")
  val width = css("width")
  val height = css("height")
  val color = css("color")
  val background = css("background")
  val backgroundColor = css("background-color")
  val backgroundImage = css("background-image")
  
  val paddingRight = css("padding-right")
  val paddingLeft = css("padding-left")
  val paddingTop = css("padding-top")
  val paddingBottom = css("padding-bottom")
  val padding = css("padding")
  
  val marginRight = css("margin-right")
  val marginLeft = css("margin-left")
  val marginTop = css("margin-top")
  val marginBottom = css("margin-bottom")
  val margin = css("margin")
  
  val borderRight = css("border-right")
  val borderLeft = css("border-left")
  val borderTop = css("border-top")
  val borderBottom = css("border-bottom")
  val border = css("border")
  val borderColor = css("border-color")
  val borderRadius = css("border-radius")
  
  val outline = css("outline")
  
  val letterSpacing = css("letter-spacing")
  val textTransform = css("textTransform")
  val backgroundPosition = css("background-position")
  val lineHeight = css("line-height")
  val font = css("font")
  val fontStyle = css("font-style")
  val fontSize = css("font-size")
  val fontWeight = css("font-weight")
  val fontFamily = css("font-family")
  val clip = css("clip")
  val zIndex = css("z-index")
  val content = css("content")
  
  val verticalAlign = css("vertical-align")
  
  val top = css("top")
  val bottom = css("bottom")
  val left = css("left")
  val right = css("right")
  
  val minWidth = css("min-width")
  val maxWidth = css("max-width")  
  val minHeight = css("min-height")
  val maxHeight = css("max-height")
  
  val whiteSpace = css("whiteSpace")
  val overflow = css("overflow")
  val textOverflow = css("textOverflow")

  val clear = css("clear")
  val float = css("float")
  val textDecoration = css("textDecoration")
  
  val cursor = css("cursor")
  
}
/*
object svg {
  object < {
    val path = Element("path", Nil(), Nil(), Nil())
  }
}*/
