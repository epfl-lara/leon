package leon.webDSL.webDescription

import leon.annotation._

@isabelle.typ(name = "Leon_Types.web_site")
@isabelle.constructor(name = "Leon_Types.web_site.Web_Site")
case class WebSite(main: leon.collection.List[WebPage])

@isabelle.typ(name = "Leon_Types.web_site_ided")
@isabelle.constructor(name = "Leon_Types.web_site_ided.Web_Site_IDed")
case class WebSiteWithIDedContent(main: leon.collection.List[WebPageWithIDedWebElements])
