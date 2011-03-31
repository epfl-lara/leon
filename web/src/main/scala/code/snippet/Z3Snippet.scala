package code
package snippet

import scala.xml.{NodeSeq,Text}

class Z3Snippet {
  def versionString(xhtml : NodeSeq) : NodeSeq = {
    Text(z3.scala.version)
  }
}
