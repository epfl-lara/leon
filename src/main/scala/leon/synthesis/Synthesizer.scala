package leon
package synthesis

import purescala.Common._
import purescala.Definitions.{Program, FunDef}
import purescala.TreeOps._
import purescala.Trees.{Expr, Not}
import purescala.ScalaPrinter

import Extensions.Solver
import java.io.File

import collection.mutable.PriorityQueue

class Synthesizer(val r: Reporter, val solvers: List[Solver]) {
  import r.{error,warning,info,fatalError}

  private[this] var solution: Option[Solution] = None
  private[this] var derivationTree: DerivationTree = _

  var derivationCounter = 1;

  def synthesize(p: Problem, rules: List[Rule]): Solution = {

    val workList = new PriorityQueue[Task]()
    val rootTask = new RootTask(this, p)


    workList += rootTask
    solution = None
    derivationTree = new DerivationTree(rootTask)

    while (!workList.isEmpty && solution.isEmpty) {
      val task = workList.dequeue()

      info("Now handling: "+task.problem)

      val alternatives = rules.flatMap(_.isApplicable(task))

      alternatives.find(_.isSuccess) match {
        case Some(ss) =>
          info(" => Rule "+ss.rule+" succeeded")
          ss.succeeded()
        case None =>
          info(" => Possible Next Steps:")
          alternatives.foreach(t => info(" -   "+t.description))
          workList ++= alternatives.flatMap(_.subTasks)
      }

      // We are stuck
      if (alternatives.isEmpty) {
        val sol = Solution.choose(task.problem)
        warning(" => I give up: "+task.problem+" ⊢  "+sol)
        onTaskSucceeded(task, sol)
      }
    }


    derivationTree.toDotFile("derivation"+derivationCounter+".dot")
    derivationCounter += 1

    solution.getOrElse(Solution.none)
  }

  def onTaskSucceeded(task: Task, solution: Solution) {
    info(" => Solved "+task.problem+" ⊢  "+solution)
    derivationTree.recordSolutionFor(task, solution)

    if (task.parent eq null) {
      info(" SUCCESS!")
      this.solution = Some(solution)
    } else {
      task.parent.subSucceeded(task.problem, solution)
    }
  }

  def solveSAT(phi: Expr): (Option[Boolean], Map[Identifier, Expr]) = {
    for (s <- solvers) {
      s.solveOrGetCounterexample(Not(phi)) match {
        case (Some(true), _) =>
          return (Some(false), Map())
        case (Some(false), model) =>
          return (Some(true), model)
        case _ =>
      }
    }
    (None, Map())
  }

  import purescala.Trees._
  def synthesizeAll(program: Program): Map[Choose, Solution] = {

    solvers.foreach(_.setProgram(program))

    val rules = Rules.all(this)

    def noop(u:Expr, u2: Expr) = u

    var solutions = Map[Choose, Solution]()

    def actOnChoose(f: FunDef)(e: Expr, a: Expr): Expr = e match {
      case ch @ Choose(vars, pred) =>
        val xs = vars
        val as = (variablesOf(pred)--xs).toList
        val phi = pred

        info("")
        info("")
        info("In Function "+f.id+":")
        info("-"*80)

        val sol = synthesize(Problem(as, phi, xs), rules)

        solutions += ch -> sol

        info("Scala code:")
        info(ScalaPrinter(simplifyLets(sol.toExpr)))

        a
      case _ =>
        a
    }

    // Look for choose()
    for (f <- program.definedFunctions.sortBy(_.id.toString) if f.body.isDefined) {
      treeCatamorphism(x => x, noop, actOnChoose(f), f.body.get)
    }

    solutions
  }


  def substitueChooses(str: String, solutions: Map[Choose, Solution], ignoreMissing: Boolean = false): String = {
    var lines = List[Int]()

    // Compute line positions
    var lastFound = -1
    do {
      lastFound = str.indexOf('\n', lastFound+1)

      if (lastFound > -1) {
        lines = lastFound :: lines
      }
    } while(lastFound> 0)
    lines = lines.reverse;

    def lineOf(offset: Int): (Int, Int) = {
      lines.zipWithIndex.find(_._1 > offset) match {
        case Some((off, no)) =>
          (no+1, if (no > 0) lines(no-1) else 0)
        case None =>
          (lines.size+1, lines.lastOption.getOrElse(0))
      }
    }

    lastFound = -1

    var newStr = str
    var newStrOffset = 0

    do {
      lastFound = str.indexOf("choose", lastFound+1)

      if (lastFound > -1) {
        val (lineno, lineoffset) = lineOf(lastFound)
        // compute scala equivalent of the position:
        val scalaOffset = str.substring(lineoffset, lastFound).replaceAll("\t", " "*8).length

        solutions.find(_._1.posIntInfo == (lineno, scalaOffset)) match {
          case Some((choose, solution)) =>
            var lvl      = 0;
            var i        = lastFound + 6;
            var continue = true;
            do {
              val c = str.charAt(i)
              if (c == '(' || c == '{') {
                lvl += 1
              } else if (c == ')' || c == '}') {
                lvl -= 1
                if (lvl == 0) {
                  continue = false
                }
              }
              i += 1
            } while(continue)

            val newCode = solutionToString(solution)
            newStr = (newStr.substring(0, lastFound+newStrOffset))+newCode+(newStr.substring(i+newStrOffset, newStr.length))

            newStrOffset += -(i-lastFound)+newCode.length

          case _ =>
            if (!ignoreMissing) {
              warning("Could not find solution corresponding to choose at "+lineno+":"+scalaOffset)
            }
        }
      }
    } while(lastFound> 0)

    newStr
  }

  def solutionToString(solution: Solution): String = {
    ScalaPrinter(simplifyLets(solution.toExpr))
  }

  def updateFile(origFile: File, solutions: Map[Choose, Solution], ignoreMissing: Boolean = false) {
    import java.io.{File, BufferedWriter, FileWriter}
    val FileExt = """^(.+)\.([^.]+)$""".r

    origFile.getAbsolutePath() match {
      case FileExt(path, "scala") =>
        var i = 0
        def savePath = path+"."+i+".scala"
        while (new File(savePath).isFile()) {
          i += 1
        }

        val origCode = readFile(origFile)
        val backup   = new File(savePath)
        val newFile  = new File(origFile.getAbsolutePath())
        origFile.renameTo(backup)


        val newCode = substitueChooses(origCode, solutions, ignoreMissing)

        val out = new BufferedWriter(new FileWriter(newFile))
        out.write(newCode)
        out.close
      case _ =>

    }
  }

  def readFile(file: File): String = {
    scala.io.Source.fromFile(file).mkString
  }
}
