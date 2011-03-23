package funcheck

import purescala.Trees._

trait CodeGeneration {
  self: CallTransformation =>
  import global._

  private lazy val serializationModule = definitions.getClass("funcheck.Serialization")
  private lazy val readProgramFunction = definitions.getMember(serializationModule, "readProgram")
  private lazy val purescalaPackage = definitions.getModule("purescala")
  private lazy val definitionsModule = definitions.getModule("purescala.Definitions")
  private lazy val programClass = definitions.getClass("purescala.Definitions.Program")
  private lazy val fairZ3SolverClass = definitions.getClass("purescala.FairZ3Solver")
  private lazy val decideWithModelFunction = definitions.getMember(fairZ3SolverClass, "decideWithModel")
  private lazy val setProgramFunction = definitions.getMember(fairZ3SolverClass, "setProgram")

  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  class CodeGenerator(unit: CompilationUnit, owner: Symbol) {
    /*
    def exprToTree(expr: Expr) : Tree = expr match {
      case Variable(id) => 
    }
    */

    def generateProgramRead(filename: String) : (Tree, Symbol) = {
      val progSymbol = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "prog")).setInfo(programClass.tpe)
      val readStatement =
        ValDef(
          progSymbol,
          Apply(
            Select(
              Ident(serializationModule),
              readProgramFunction
            ),
            List(Literal(Constant(filename)))
          )
        )
      (readStatement, progSymbol)
    }

    def generateSolverInvocation(formula: Expr) : Tree = {
      val solverSymbol = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "solver")).setInfo(fairZ3SolverClass.tpe)
      val solverDeclaration = 
        ValDef(
          solverSymbol,
          New(
            Ident(fairZ3SolverClass),
            List(
              List(
                New(
                  Ident(defaultReporter),
                  List(Nil)
                )
              )
            )
          )
        )
      val setProgram =
        Apply(
          Select(
            Ident(solverSymbol),
            setProgramFunction
          ),
          List(/* read program into a var and plug its symbol here */)
        )

      val invocation =
        Apply(
          Select(
            Ident(solverSymbol),
            decideWithModelFunction
          ),
          List(/* convert pred into scala AST and plug it here */)
        )

      Block(
            solverDeclaration :: setProgram :: invocation :: Nil,
            Literal(Constant(0))
          )
    }
  }
}
