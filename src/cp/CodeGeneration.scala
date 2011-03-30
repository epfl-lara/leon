package cp

import purescala.Trees._

trait CodeGeneration {
  self: CallTransformation =>
  import global._
  import CODE._

  private lazy val exceptionClass = definitions.getClass("java.lang.Exception")

  private lazy val cpPackage = definitions.getModule("cp")

  private lazy val serializationModule = definitions.getModule("cp.Serialization")
  private lazy val getProgramFunction = definitions.getMember(serializationModule, "getProgram")
  private lazy val getExprFunction = definitions.getMember(serializationModule, "getExpr")

  private lazy val purescalaPackage = definitions.getModule("purescala")

  private lazy val definitionsModule = definitions.getModule("purescala.Definitions")
  private lazy val programClass = definitions.getClass("purescala.Definitions.Program")

  private lazy val treesModule = definitions.getModule("purescala.Trees")
  private lazy val exprClass = definitions.getClass("purescala.Trees.Expr")
  private lazy val intLiteralClass = definitions.getClass("purescala.Trees.IntLiteral")
  private lazy val intLiteralModule = definitions.getModule("purescala.Trees.IntLiteral")

  private lazy val fairZ3SolverClass = definitions.getClass("purescala.FairZ3Solver")
  private lazy val restartAndDecideWithModel = definitions.getMember(fairZ3SolverClass, "restartAndDecideWithModel")
  private lazy val setProgramFunction = definitions.getMember(fairZ3SolverClass, "setProgram")

  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  class CodeGenerator(unit : CompilationUnit, owner : Symbol) {

    def getProgram(filename : String) : (Tree, Symbol) = {
      val progSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "prog")).setInfo(programClass.tpe)
      val getStatement = VAL(progSym) === ((cpPackage DOT serializationModule DOT getProgramFunction) APPLY LIT(filename))
      (getStatement, progSym)
    }

    def getExpr(filename : String) : (Tree, Symbol) = {
      val exprSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "expr")).setInfo(exprClass.tpe)
      val getStatement = VAL(exprSym) === ((cpPackage DOT serializationModule DOT getExprFunction) APPLY LIT(filename))
      (getStatement, exprSym)
    }

    def invokeSolver(progSym : Symbol, exprSym : Symbol) : Tree = {
      val solverSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "solver")).setInfo(fairZ3SolverClass.tpe)
      val solverDeclaration = VAL(solverSym) === NEW(ID(fairZ3SolverClass), NEW(ID(defaultReporter)))
      val setProgram = (solverSym DOT setProgramFunction) APPLY ID(progSym)
      val invocation = (solverSym DOT restartAndDecideWithModel) APPLY (ID(exprSym), LIT(false))

      BLOCK(solverDeclaration, setProgram, invocation, LIT(0))
    }

    def exprToScala(owner : Symbol) : (Symbol, Tree) = {
      val methodSym = owner.newMethod(NoPosition, unit.fresh.newName(NoPosition, "exprToScala"))
      methodSym.setInfo(MethodType(methodSym.newSyntheticValueParams(List(definitions.AnyClass.tpe)), definitions.AnyClass.tpe))
      owner.info.decls.enter(methodSym)

      val intSym = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.IntClass.tpe)

      val matchExpr = (methodSym ARG 0) MATCH (
        CASE((intLiteralModule) APPLY (intSym BIND WILD())) ==> ID(intSym) ,
        DEFAULT                                             ==> THROW(exceptionClass, LIT("Cannot convert FunCheck expression to Scala term"))
      )

      (methodSym, DEF(methodSym) === matchExpr)
    }

    def invokeExprToScala(methodSym : Symbol) : Tree = {
      methodSym APPLY ()
    }
  }
}
