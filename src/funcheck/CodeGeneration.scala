package funcheck

import purescala.Trees._

trait CodeGeneration {
  self: CallTransformation =>
  import global._

  private lazy val funcheckPackage = definitions.getModule("funcheck")

  private lazy val serializationModule = definitions.getModule("funcheck.Serialization")
  private lazy val getProgramFunction = definitions.getMember(serializationModule, "getProgram")
  private lazy val getExprFunction = definitions.getMember(serializationModule, "getExpr")

  private lazy val purescalaPackage = definitions.getModule("purescala")

  private lazy val definitionsModule = definitions.getModule("purescala.Definitions")
  private lazy val programClass = definitions.getClass("purescala.Definitions.Program")

  private lazy val treesModule = definitions.getModule("purescala.Trees")
  private lazy val exprClass = definitions.getClass("purescala.Trees.Expr")

  private lazy val fairZ3SolverClass = definitions.getClass("purescala.FairZ3Solver")
  private lazy val restartAndDecideWithModel = definitions.getMember(fairZ3SolverClass, "restartAndDecideWithModel")
  private lazy val setProgramFunction = definitions.getMember(fairZ3SolverClass, "setProgram")

  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  class CodeGenerator(unit : CompilationUnit, owner : Symbol) {

    def generateProgramGet(filename : String) : (Tree, Symbol) = {
      val progSymbol = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "prog")).setInfo(programClass.tpe)
      val getStatement =
        ValDef(
          progSymbol,
          Apply(
            Select(
              Select(
                Ident(funcheckPackage),
                serializationModule
              ) ,
              getProgramFunction
            ),
            List(Literal(Constant(filename)))
          )
        )
      (getStatement, progSymbol)
    }

    def generateExprGet(filename : String) : (Tree, Symbol) = {
      val exprSymbol = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "expr")).setInfo(exprClass.tpe)
      val getStatement =
        ValDef(
          exprSymbol,
          Apply(
            Select(
              Select(
                Ident(funcheckPackage),
                serializationModule
              ),
              getExprFunction
            ),
            List(Literal(Constant(filename)))
          )
        )
      (getStatement, exprSymbol)
    }

    def generateSolverInvocation(formula : Expr, progSymbol : Symbol, exprSymbol : Symbol) : Tree = {
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
          List(Ident(progSymbol))
        )

      val invocation =
        Apply(
          Select(
            Ident(solverSymbol),
            restartAndDecideWithModel
          ),
          List(Ident(exprSymbol), Literal(Constant(false)))
        )

      Block(
            solverDeclaration :: setProgram :: invocation :: Nil,
            Literal(Constant(0))
          )
    }
  }
}
