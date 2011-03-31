/*package code
package comet
 
import net.liftweb._
import http._
import actor._
import util.Helpers._
import js._
import JsCmds._
import JE._
 
object ChatServer extends LiftActor with ListenerManager {
  private var messages = Vector("Welcome")
 
  def createUpdate = messages
 
  override def lowPriority = {
    case s: String => messages :+= s; updateListeners()
  }
}
 
class Chat extends CometActor with CometListener {
  private var msgs: Vector[String] = Vector()
 
  def registerWith = ChatServer
 
  override def lowPriority = {
    case v: Vector[String] => msgs = v; reRender()
  }
 
  def render = "li *" #> msgs
 
  override def fixedRender = {
    <lift:form>
    {
      SHtml.text("", s => {
        ChatServer ! s
        SetValById("chat_box", "")
      }, "id" -> "chat_box")
    }
    <input type="submit" value="Chat"/>
    </lift:form>
  }
 
}

*/
