/* Copyright 2009-2013 EPFL, Lausanne */

package leon.synthesis.search

import akka.actor._
import scala.concurrent.duration._
import scala.concurrent.Await
import akka.util.Timeout
import akka.pattern.ask
import akka.pattern.AskTimeoutException

abstract class AndOrGraphParallelSearch[WC,
                                        AT <: AOAndTask[S],
                                        OT <: AOOrTask[S],
                                        S](og: AndOrGraph[AT, OT, S],
                                           nWorkers: Int) extends AndOrGraphSearch[AT, OT, S](og) {

  def initWorkerContext(w: ActorRef): WC

  val timeout = 600.seconds

  var system: ActorSystem = _

  def search(): Option[(S, Boolean)] = {
    system = ActorSystem("ParallelSearch")

    val master = system.actorOf(Props(new Master), name = "Master")

    val workers = for (i <- 1 to nWorkers) yield {
      system.actorOf(Props(new Worker(master)), name = "Worker"+i)
    }

    try {
      Await.result(master.ask(Protocol.BeginSearch)(timeout), timeout)
    } catch {
      case e: AskTimeoutException =>
    }

    if (system ne null) {
      system.shutdown
      system = null
    }

    g.tree.solution.map(s => (s, g.tree.isTrustworthy))
  }

  override def stop() {
    super.stop()

    if(system ne null) {
      system.shutdown
      system = null
    }
  }


  object Protocol {
    case object BeginSearch
    case object SearchDone

    case class WorkerNew(worker: ActorRef)
    case class WorkerAndTaskDone(worker: ActorRef, res: ExpandResult[OT])
    case class WorkerOrTaskDone(worker: ActorRef, res: ExpandResult[AT])

    case class RequestAndTask(task: AT)
    case class RequestOrTask(task: OT)
    case object NoTaskReady
  }

  def getNextLeaves(idleWorkers: Map[ActorRef, Option[g.Leaf]], workingWorkers: Map[ActorRef, Option[g.Leaf]]): List[g.Leaf] = {
    val processing = workingWorkers.values.flatten.toSet

    val ts = System.currentTimeMillis();

    val str = nextLeaves()
      .filterNot(processing)
      .take(idleWorkers.size)
      .toList

    str
  }

  class Master extends Actor {
    import Protocol._

    var outer: ActorRef = _

    var workers = Map[ActorRef, Option[g.Leaf]]()

    def sendWork() {
      val (idleWorkers, workingWorkers) = workers.partition(_._2.isEmpty)

      assert(idleWorkers.size > 0)

      getNextLeaves(idleWorkers, workingWorkers) match {
        case Nil =>
          if (workingWorkers.isEmpty) {
            outer ! SearchDone
          } else {
            // No work yet, waiting for results from ongoing work
          }

        case ls =>
          for ((w, leaf) <- idleWorkers.keySet zip ls) {
            leaf match {
              case al: g.AndLeaf =>
                workers += w -> Some(al)
                w ! RequestAndTask(al.task)
              case ol: g.OrLeaf =>
                workers += w -> Some(ol)
                w ! RequestOrTask(ol.task)
            }
          }
      }
    }

    context.setReceiveTimeout(10.seconds)

    def receive = {
      case BeginSearch =>
        outer = sender

      case WorkerNew(w) =>
        workers += w -> None
        context.watch(w)
        sendWork()

      case WorkerAndTaskDone(w, res) =>
        workers.get(w) match {
          case Some(Some(l: g.AndLeaf)) =>
            onExpansion(l, res)
            workers += w -> None
          case _ =>
        }
        sendWork()

      case WorkerOrTaskDone(w, res) =>
        workers.get(w) match {
          case Some(Some(l: g.OrLeaf)) =>
            onExpansion(l, res)
            workers += w -> None
          case _ =>
        }
        sendWork()

      case Terminated(w) =>
        if (workers contains w) {
          workers -= w
        }

      case ReceiveTimeout =>
        println("@ Worker status:")
        for ((w, t) <- workers if t.isDefined) {
          println("@  - "+w.toString+": "+t.get.task)
        }


    }
  }

  class Worker(master: ActorRef) extends Actor {
    import Protocol._

    val ctx = initWorkerContext(self)

    def receive = {
      case RequestAndTask(at) =>
        val res = expandAndTask(self, ctx)(at)
        master ! WorkerAndTaskDone(self, res)

      case RequestOrTask(ot) =>
        val res = expandOrTask(self, ctx)(ot)
        master ! WorkerOrTaskDone(self, res)
    }

    override def preStart() = master ! WorkerNew(self)
  }

  def expandAndTask(w: ActorRef, ctx: WC)(t: AT): ExpandResult[OT]

  def expandOrTask(w: ActorRef, ctx: WC)(t: OT): ExpandResult[AT]
}
