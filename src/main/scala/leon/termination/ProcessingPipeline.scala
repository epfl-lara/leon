/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package termination

import purescala.Expressions._
import purescala.Definitions._
import utils._

trait Problem {
  def funSet: Set[FunDef]
  def funDefs: Seq[FunDef]
  def contains(fd: FunDef): Boolean = funSet(fd)

  override def toString : String = funDefs.map(_.id).mkString("Problem(", ",", ")")
}

object Problem {
  def apply(fds: Set[FunDef]): Problem = new Problem {
    val funSet = fds
    lazy val funDefs = funSet.toSeq
  }

  def apply(fds: Seq[FunDef]): Problem = new Problem {
    val funDefs = fds
    lazy val funSet = funDefs.toSet
  }
}

sealed abstract class Result(funDef: FunDef)
case class Cleared(funDef: FunDef) extends Result(funDef)
case class Broken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)
case class MaybeBroken(funDef: FunDef, args: Seq[Expr]) extends Result(funDef)

abstract class ProcessingPipeline(context: LeonContext, program: Program) extends TerminationChecker(context, program) {
  implicit val debugSection = utils.DebugSectionTermination

  import scala.collection.mutable.{PriorityQueue, Map => MutableMap, Set => MutableSet}

  def processors: List[Processor]

  private lazy val processorArray: Array[Processor] = {
    assert(processors.nonEmpty)
    processors.toArray
  }

  private val reporter: Reporter = context.reporter

  implicit object ProblemOrdering extends Ordering[(Problem, Int)] {
    def compare(a: (Problem, Int), b: (Problem, Int)): Int = {
      val ((aProblem, aIndex), (bProblem, bIndex)) = (a,b)
      val (aDefs, bDefs) = (aProblem.funSet, bProblem.funSet)

      val aCallees: Set[FunDef] = aDefs.flatMap(program.callGraph.transitiveCallees)
      val bCallees: Set[FunDef] = bDefs.flatMap(program.callGraph.transitiveCallees)

      lazy val aCallers: Set[FunDef] = aDefs.flatMap(program.callGraph.transitiveCallers)
      lazy val bCallers: Set[FunDef] = bDefs.flatMap(program.callGraph.transitiveCallers)

      val aCallsB = bDefs.subsetOf(aCallees)
      val bCallsA = aDefs.subsetOf(bCallees)

      if (aCallsB && !bCallsA) {
        -1
      } else if (bCallsA && !aCallsB) {
        1
      } else {
        val smallerPool = bCallees.size compare aCallees.size
        if (smallerPool != 0) smallerPool else {
          val largerImpact = aCallers.size compare bCallers.size
          if (largerImpact != 0) largerImpact else {
            bIndex compare aIndex
          }
        }
      }
    }
  }

  private val problems = new PriorityQueue[(Problem, Int)]
  def running = problems.nonEmpty

  private val clearedMap     : MutableMap[FunDef, String]              = MutableMap.empty
  private val brokenMap      : MutableMap[FunDef, (String, Seq[Expr])] = MutableMap.empty
  private val maybeBrokenMap : MutableMap[FunDef, (String, Seq[Expr])] = MutableMap.empty

  private val unsolved     : MutableSet[Problem] = MutableSet.empty
  private val dependencies : MutableSet[Problem] = MutableSet.empty

  def isProblem(fd: FunDef): Boolean =
    unsolved.exists(_.contains(fd)) ||
    dependencies.exists(_.contains(fd)) || {
      val problemDefs = problems.flatMap(_._1.funDefs).toSet
      problemDefs(fd) || {
        val callees = program.callGraph.transitiveCallees(fd)
        (problemDefs intersect callees).nonEmpty
      }
    }

  private def printQueue() {
    val sb = new StringBuilder()
    sb.append("- Problems in Queue:\n")
    for(p @ (problem, index) <- problems) {
      sb.append("  -> Problem awaiting processor #")
      sb.append(index + 1)
      sb.append(" (")
      sb.append(processorArray(index).name)
      sb.append(")")
      if (p == problems.head) sb.append(" <- next")
      sb.append("\n")
      for(funDef <- problem.funDefs) {
        sb.append("      " + funDef.id + "\n")
      }
    }
    reporter.debug(sb.toString)
  }

  private def printResult(results: List[Result]) {
    val sb = new StringBuilder()
    sb.append("- Processing Result:\n")
    for(result <- results) result match {
      case Cleared(fd) => sb.append(f"    ${fd.id}%-10s Cleared\n")
      case Broken(fd, args) => sb.append(f"    ${fd.id}%-10s ${"Broken for arguments: " + args.mkString("(", ",", ")")}\n")
      case MaybeBroken(fd, args) => sb.append(f"    ${fd.id}%-10s ${"HO construct application breaks for arguments: " + args.mkString("(", ",", ")")}\n")
    }
    reporter.debug(sb.toString)
  }

  private val terminationMap : MutableMap[FunDef, TerminationGuarantee] = MutableMap.empty
  def terminates(funDef: FunDef): TerminationGuarantee = terminationMap.get(funDef) match {
    case Some(guarantee) => guarantee
    case None =>
      val guarantee = brokenMap.get(funDef) match {
        case Some((reason, args)) => LoopsGivenInputs(reason, args)
        case None => maybeBrokenMap.get(funDef) match {
          case Some((reason, args)) => MaybeLoopsGivenInputs(reason, args)
          case None =>
            val callees = program.callGraph.transitiveCallees(funDef)
            val broken = brokenMap.keys.toSet ++ maybeBrokenMap.keys
            callees intersect broken match {
              case set if set.nonEmpty => CallsNonTerminating(set)
              case _ if isProblem(funDef) => NoGuarantee
              case _ => clearedMap.get(funDef) match {
                case Some(reason) => Terminates(reason)
                case None if !running =>
                  verifyTermination(funDef)
                  terminates(funDef)
                case _ =>
                  if (!dependencies.exists(_.contains(funDef))) {
                    dependencies ++= generateProblems(funDef)
                  }
                  NoGuarantee
              }
            }
        }
      }

      if (!running) terminationMap(funDef) = guarantee
      guarantee
  }

  private def generateProblems(funDef: FunDef): Seq[Problem] = {
    val funDefs = program.callGraph.transitiveCallees(funDef) + funDef
    val pairs = program.callGraph.allCalls.filter { case (fd1, fd2) => funDefs(fd1) && funDefs(fd2) }
    val callGraph = pairs.groupBy(_._1).mapValues(_.map(_._2))
    val components = SCC.scc(callGraph)

    for (fd <- funDefs -- components.toSet.flatten) clearedMap(fd) = "Non-recursive"

    components.map(fds => Problem(fds.toSeq))
  }

  def verifyTermination(funDef: FunDef): Unit = {
    problems ++= generateProblems(funDef).map(_ -> 0)

    val it = new Iterator[(String, List[Result])] {
      def hasNext : Boolean      = running
      def next()  : (String, List[Result]) = {
        printQueue()
        val (problem, index) = problems.head
        val processor : Processor = processorArray(index)
        reporter.debug("Running " + processor.name)
        val result = processor.run(problem)
        reporter.debug(" +-> " + (if (result.isDefined) "Success" else "Failure"))

        // dequeue and enqueue atomically to make sure the queue always
        // makes sense (necessary for calls to terminates(fd))
        problems.dequeue()
        result match {
          case None if index == processorArray.length - 1 =>
            unsolved += problem
          case None =>
            problems.enqueue(problem -> (index + 1))
          case Some(results) =>
            val impacted = problem.funDefs.flatMap(fd => program.callGraph.transitiveCallers(fd))
            val reenter = unsolved.filter(p => (p.funDefs intersect impacted).nonEmpty)
            problems.enqueue(reenter.map(_ -> 0).toSeq : _*)
            unsolved --= reenter
        }

        if (dependencies.nonEmpty) {
          problems.enqueue(dependencies.map(_ -> 0).toSeq : _*)
          dependencies.clear
        }

        processor.name -> result.toList.flatten
      }
    }

    for ((reason, results) <- it; result <- results) result match {
      case Cleared(fd) => clearedMap(fd) = reason
      case Broken(fd, args) => brokenMap(fd) = (reason, args)
      case MaybeBroken(fd, args) => maybeBrokenMap(fd) = (reason, args)
    }
  }
}

// vim: set ts=4 sw=4 et:
