package purescala.testcases

import purescala.Reporter
import purescala.Trees._
import purescala.Definitions._
import purescala.Extensions._
import purescala.Settings
import purescala.Common.Identifier

class Main(reporter : Reporter) extends Analyser(reporter) {
  val description = "Testcase generation from preconditions"
  override val shortDescription = "testcases"

  def analyse(program : Program) : Unit = {
    // things that we could control with options:
    //   - generate for all functions or just impure
    //   - do not generate for private functions (check FunDef.isPrivate)
    //   - number of cases per function

    reporter.info("Running testcase generation...")

    val solver = new purescala.Z3Solver(reporter)
    solver.setProgram(program)
    
    def writeToFile(filename: String, content: String) : Unit = {
      try {
        val fw = new java.io.FileWriter(filename)
        fw.write(content)
        fw.close
      } catch {
        case e => reporter.error("There was an error while generating the test file" + filename)
      }
    }

    def generateTestInput(funDef: FunDef) : Seq[Seq[Expr]] = {
      var constraints: Expr = BooleanLiteral(true)
      val prec = matchToIfThenElse(funDef.precondition.getOrElse(BooleanLiteral(true)))
      var inputList: List[Seq[Expr]] = Nil
      for (i <- 1 to Settings.nbTestcases) {
        // reporter.info("Current constraints: " + constraints)
        val argMap = solver.decideIterativeWithBounds(And(prec, constraints), false)
        argMap match {
          case (Some(true), _) => None
          case (_ , map) =>
            reporter.info("Solver returned the following assignment: " + map)
            val testInput = (for (arg <- funDef.args) yield {
              map.get(arg.id) match {
                case Some(value) => value
                case None => randomValue(arg.toVariable)
              }
            })
            inputList = testInput :: inputList
            val newConstraints = And(funDef.args.map(_.toVariable).zip(testInput).map{
              case (variable, value) => Equals(variable, value)
            })
            constraints = And(constraints, negate(newConstraints))
        }
      }

      inputList.reverse
    }

    def indent(s: String) : String = "  " + s.split("\n").mkString("\n  ")
    def capitalize(s: String) : String = s.substring(0, 1).toUpperCase + s.substring(1)

    def testFunctionName(id: Identifier) : String = "test" + capitalize(id.toString)
    def testFunction(id: Identifier, inputs: Seq[Seq[Expr]]) : String = {
      val idString = id.toString
      val toReturn = 
        "def " + testFunctionName(id) + " : Unit = {" + "\n" +
        inputs.map(input => indent(idString + input.mkString("(", ", ", ")"))).mkString("\n") + "\n" +
        "}" + "\n"
      toReturn
    }

    def testMainMethod(funcIds: Seq[Identifier]) : String = {
      "def main(args: Array[String]) : Unit = {" + "\n" +
      indent(funcIds.map(testFunctionName(_)).mkString("\n")) + "\n" +
      "}" + "\n"
    }

    def testObject(funcInputPairs: Seq[(Identifier, Seq[Seq[Expr]])]) : String = {
      val objectName = program.mainObject.id.toString
      val toReturn =
        "import " + objectName + "._" + "\n" +
        "\n" +
        "object Test" + capitalize(objectName) + " {" + "\n" +
        indent(testMainMethod(funcInputPairs.map(_._1))) + "\n" +
        "\n" +
        indent(funcInputPairs.map(pair => testFunction(pair._1, pair._2)).mkString("\n")) + "\n" +
        "}"
      toReturn
    }

    val funcInputPairs: Seq[(Identifier, Seq[Seq[Expr]])] = (for (funDef <- program.definedFunctions.toList.sortWith((fd1, fd2) => fd1 < fd2) if (!funDef.isPrivate && (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name)) && (!Settings.impureTestcases || !funDef.hasBody))) yield {
      reporter.info("Considering function definition: " + funDef.id)
      funDef.precondition match {
        case Some(p) => reporter.info("The precondition is: " + p)
        case None =>    reporter.info("Function has no precondition")
      }

      val testInput = generateTestInput(funDef)
      reporter.info("Generated test input is: " + testInput)
      (funDef.id, testInput)
    })

    writeToFile("Test" + program.mainObject.id.toString + ".scala", testObject(funcInputPairs))
    
    reporter.info("Done.")
  }

}
