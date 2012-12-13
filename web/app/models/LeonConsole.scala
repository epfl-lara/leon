package leon.web
package models

import akka.actor._
import akka.util.duration._

import play.api._
import play.api.libs.json._
import play.api.libs.iteratee._
import play.api.libs.concurrent._
import play.api.libs.json.Json._
import play.api.libs.json.Writes._

import akka.util.Timeout
import akka.pattern.ask

import play.api.Play.current

import leon.{LeonContext, Settings, Reporter}
import leon.plugin.{TemporaryInputPhase, ExtractionPhase}
import leon.synthesis.SynthesisPhase
import leon.verification.AnalysisPhase

object LeonConsole {
  def open: Promise[(Iteratee[JsValue,_],Enumerator[JsValue])] = {
    import ConsoleProtocol._

    val session = Akka.system.actorOf(Props[ConsoleSession])
    implicit val timeout = Timeout(1.seconds)

    (session ? Init).asPromise.map {
      case InitSuccess(enumerator) =>
        // Create an Iteratee to consume the feed
        val iteratee = Iteratee.foreach[JsValue] { event =>
          (event \ "action").as[String] match {
            case "start" =>
              session ! Start((event \ "mode").as[String], (event \ "code").as[String])
            case "stop" =>
              session ! Stop
            case _ =>
          }
        }.mapDone { _ =>
          session ! Quit
        }

        (iteratee,enumerator)

      case InitFailure(error: String) =>
        // Connection error

        // A finished Iteratee sending EOF
        val iteratee = Done[JsValue,Unit]((),Input.EOF)

        // Send an error and close the socket
        val enumerator =  Enumerator[JsValue](toJson(
          Map("kind" -> "error", "message" -> error)
        )).andThen(Enumerator.enumInput(Input.EOF))

        (iteratee,enumerator)
    }
  }
}

class ConsoleSession extends Actor {
  import ConsoleProtocol._

  var isStarted = false
  var channel: PushEnumerator[JsValue] = _
  var reporter: WSReporter = _

  def log(msg: String) = {
    channel.push(toJson(Map("kind" -> "log", "message" -> msg)))
  }

  def error(msg: String) = {
    channel.push(toJson(Map("kind" -> "error", "message" -> msg)))
  }

  def event(kind: String) = {
    channel.push(toJson(Map("kind" -> "event", "event" -> kind)))
  }

  def receive = {
    case Init =>
      channel = Enumerator.imperative[JsValue]()
      reporter = WSReporter(channel)
      sender ! InitSuccess(channel)

    case Start(mode, code) =>
      log("Welcome to LeonOnline!")
      log("Processing request...")

      val classPath = Play.current.configuration.getString("app.classpath").map(_.split(":").toList).getOrElse(Settings.defaultClassPath())

      mode match {
        case "verification" =>
          event("started")
          isStarted = true

          var ctx = leon.Main.processOptions(reporter, "--timeout=2" :: Nil)
          ctx = ctx.copy(settings = ctx.settings.copy(classPath = classPath))

          val pipeline = TemporaryInputPhase andThen ExtractionPhase andThen AnalysisPhase

          pipeline.run(ctx)((code, Nil))

          event("stopped")

        case "synthesis" =>
          event("started")
          isStarted = true

          var ctx = leon.Main.processOptions(reporter, "--synthesis" :: "--parallel" :: "--timeout=10" :: Nil)
          ctx = ctx.copy(settings = ctx.settings.copy(classPath = classPath))

          val pipeline = TemporaryInputPhase andThen ExtractionPhase andThen SynthesisPhase

          pipeline.run(ctx)((code, Nil))

          event("stopped")

        case _ =>
          error("Invalid request mode: "+mode)
      }


    case Stop =>
      isStarted = false

      event("stopped")
    case Quit =>

  }
}

object ConsoleProtocol {
  case object Init
  case class InitSuccess(enum: Enumerator[JsValue])
  case class InitFailure(error: String)


  case class Start(mode: String, code: String)

  case object Stop

  case object Quit
}

case class WSReporter(channel: PushEnumerator[JsValue]) extends Reporter {
  def infoFunction(msg: Any) : Unit = {
    channel.push(toJson(Map("kind" -> "log", "message" -> (msg.toString))))
  }

  def warningFunction(msg: Any) : Unit = {
    channel.push(toJson(Map("kind" -> "log", "message" -> ("Warning: "+msg.toString))))
  }

  def errorFunction(msg: Any) : Unit = {
    channel.push(toJson(Map("kind" -> "log", "message" -> ("Error: "+msg.toString))))
  }

  def fatalErrorFunction(msg: Any) : Nothing = {
    sys.error("FATAL: "+msg)
  }
}

