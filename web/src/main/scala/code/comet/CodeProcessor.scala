package code
package comet

import scala.xml._

import scala.actors._
import scala.actors.Actor._

import net.liftweb._
import net.liftweb.common._
import net.liftweb.http._
import net.liftweb.actor._
import net.liftweb.util.Helpers._
import net.liftweb.http.js._
import net.liftweb.http.js.JsCmds._
import net.liftweb.http.js.JE._

import purescala.Reporter
import purescala.Definitions._
import funcheck.{Main=>FuncheckMain}

// A query contains a whole program :D
case class Query(editor : CodeProcessor, string : String)
case class Message(string : String)
case object Clear

// A funcheck/purescala compliant reporter that sends the
// strings to an actor rather than printing them.
class ActorReporter(dest : CodeProcessor) extends Reporter {
  private val BUFSZ : Int = 10
  private val buffer : Array[String] = new Array[String](BUFSZ)
  private var id : Int = 0

  def output(msg : Any) : Unit = {
    val str = msg.toString
    val trimmed = str.trim
    val exclude = trimmed.startsWith("-") || trimmed.startsWith("Trying")

    if(!exclude) {
      buffer(id) = str
      id += 1
      if(id == BUFSZ) {
        send()
        id = 0
      }
    }
  }

  def flush : Unit = {
    send(id)
    id = 0
  }

  private def send(num : Int = BUFSZ) : Unit = {
    val msg = buffer.take(num).mkString("\n")
    dest ! Message(msg)
  }

  def error(msg: Any) = output(msg)
  def warning(msg: Any) = output(msg)
  def info(msg: Any) = output(msg)
  def fatalError(msg: Any) = {
    output(msg)
    throw new Exception("Fatal error.")
  }
}

object QueryHandler extends LiftActor {
  private val cpdir = "/localhome/liftweb/leonscalaccp/"
  private val classpath = List(
    cpdir + "scala-library.jar" + ":" +
    cpdir + "funcheck.jar"
  )
  private val funcheckOptions : Array[String] = Array(
    "--CAV",
    "--timeout=5"
  )

  def messageHandler = {
    case Query(editor, string) => {
      editor ! Clear
      editor ! Message("Query received.")
      editor ! Message("")

      val reporter = new ActorReporter(editor)
      try {
        FuncheckMain.runFromString(string, funcheckOptions, reporter, Some(classpath))
      } catch {
        case e : Exception => editor ! Message(e.getMessage)
      }
      reporter.flush
      editor ! Message("Done.")
    }
  }
}

class CodeProcessor extends CometActor {
  override def defaultPrefix = Full("codeprocessor")
  private var msgs : List[String] = Nil

  override def lowPriority : PartialFunction[Any,Unit] = {
    case Clear => {
      msgs = Nil
      partialUpdate(
        SetValById("consolebox", "Cleared.")
      )
    }

    case Message(msg) => {
      msgs = msg :: msgs
      partialUpdate(
        SetValById("consolebox", msgs.reverse.mkString("\n"))
      )
    }
  }

  def render = <span></span>

  override def fixedRender = bind("inputbox" ->
      <lift:form>
        {
          SHtml.textarea("", s => {
              QueryHandler ! Query(this, s)
            }, "id" -> "codebox")
        }
        {
          SHtml.submit("Verify !", () => {}, "id" -> "clicker", "onClick" -> "editor.save();")
        }
        {
          SHtml.textarea("Console.\n", s => {}, "id" -> "consolebox", "onChange" -> "document.getElementById('consolebox').scrollTop=document.getElementById('consolebox').scrollHeight;")
        }
      </lift:form>
    )
}
