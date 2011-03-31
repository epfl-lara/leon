/*
package code
package comet

import scala.actors._
import scala.actors.Actor._

import net.liftweb._
import net.liftweb.http._
import net.liftweb.actor._
import net.liftweb.util.Helpers._
import net.liftweb.http.js._
import net.liftweb.http.js.JsCmds._
import net.liftweb.http.js.JE._

case class Query(editor : Editor, string : String)
case class Ack(string : String)

object QueryHandler extends LiftActor {

  def messageHandler = {
    case Query(editor, string) => {
      val shorter = if(string.length > 5) {
        string.substring(0,5) + "..."
      } else {
        string
      }
      editor ! Ack("I got your message: " + shorter)
    }
  }
}

class Editor extends CometActor {
  private var msgs : List[String] = List("first msg.")

  override def lowPriority : PartialFunction[Any,Unit] = {
    case Ack(msg) => msgs = msg :: msgs; reRender()
  }

  def render = "li *" #> msgs

  override def fixedRender = {
      <lift:form>
        {
          SHtml.textarea("", s => {
              QueryHandler ! Query(this, s)
            }, "id" -> "code_box", "cols" -> "120", "rows" -> "40")
        }
        <input type="submit" onClick="editor.save();" value="Code" />
      </lift:form>
  }
}

*/
