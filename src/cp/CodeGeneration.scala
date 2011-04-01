package cp

import purescala.Trees._
import purescala.Definitions._

trait CodeGeneration {
  self: CallTransformation =>
  import global._
  import CODE._

  private lazy val scalaPackage = definitions.ScalaPackage

  private lazy val exceptionClass = definitions.getClass("java.lang.Exception")

  private lazy val mapFunction = definitions.getMember(definitions.ListClass, "map")

  private lazy val mapClass = definitions.getClass("scala.collection.immutable.Map")

  private lazy val cpPackage = definitions.getModule("cp")

  private lazy val callTransformationModule  = definitions.getModule("cp.CallTransformation")
  private lazy val outputAssignmentsFunction = definitions.getMember(callTransformationModule, "outputAssignments")
  private lazy val modelFunction             = definitions.getMember(callTransformationModule, "model")
  private lazy val modelValueFunction        = definitions.getMember(callTransformationModule, "modelValue")

  private lazy val serializationModule      = definitions.getModule("cp.Serialization")
  private lazy val getProgramFunction       = definitions.getMember(serializationModule, "getProgram")
  private lazy val getExprFunction          = definitions.getMember(serializationModule, "getExpr")
  private lazy val getOutputVarListFunction = definitions.getMember(serializationModule, "getOutputVarList")

  private lazy val purescalaPackage = definitions.getModule("purescala")

  private lazy val definitionsModule = definitions.getModule("purescala.Definitions")
  private lazy val programClass      = definitions.getClass("purescala.Definitions.Program")

  private lazy val commonModule    = definitions.getModule("purescala.Common")
  private lazy val identifierClass = definitions.getClass("purescala.Common.Identifier")

  private lazy val treesModule          = definitions.getModule("purescala.Trees")
  private lazy val exprClass            = definitions.getClass("purescala.Trees.Expr")
  private lazy val intLiteralModule     = definitions.getModule("purescala.Trees.IntLiteral")
  private lazy val booleanLiteralModule = definitions.getModule("purescala.Trees.BooleanLiteral")
  private lazy val caseClassModule      = definitions.getModule("purescala.Trees.CaseClass")

  private lazy val fairZ3SolverClass         = definitions.getClass("purescala.FairZ3Solver")
  private lazy val restartAndDecideWithModel = definitions.getMember(fairZ3SolverClass, "restartAndDecideWithModel")
  private lazy val setProgramFunction        = definitions.getMember(fairZ3SolverClass, "setProgram")

  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  class CodeGenerator(unit : CompilationUnit, owner : Symbol) {

    /* Assign the program read from file `filename` to a new variable and
     * return the code and the symbol for the variable */
    def assignProgram(filename : String) : (Tree, Symbol) = {
      val progSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "prog")).setInfo(programClass.tpe)
      val getStatement = VAL(progSym) === ((cpPackage DOT serializationModule DOT getProgramFunction) APPLY LIT(filename))
      (getStatement, progSym)
    }

    /* Assign the expression read from file `filename` to a new variable and
     * return the code and the symbol for the variable */
    def assignExpr(filename : String) : (Tree, Symbol) = {
      val exprSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "expr")).setInfo(exprClass.tpe)
      val getStatement = VAL(exprSym) === ((cpPackage DOT serializationModule DOT getExprFunction) APPLY LIT(filename))
      (getStatement, exprSym)
    }

    /* Assign the list of variable names read from file `filename` to a new
     * variable and return the code and the symbol for the variable */
    def assignOutputVarList(filename : String) : (Tree, Symbol) = {
      val listSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "ovl")).setInfo(typeRef(NoPrefix, definitions.ListClass, List(definitions.StringClass.tpe)))
      val getStatement = VAL(listSym) === ((cpPackage DOT serializationModule DOT getOutputVarListFunction) APPLY LIT(filename))
      (getStatement, listSym)
    }

    /* Assign the map of strings to model values to a new variable and return
     * the code as well as the new symbol */
    def assignModel(outcomeTupleSym : Symbol) : (Tree, Symbol) = {
      val modelSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "model")).setInfo(typeRef(NoPrefix, mapClass, List(definitions.StringClass.tpe, exprClass.tpe)))
      val assignment = VAL(modelSym) === (modelFunction APPLY ID(outcomeTupleSym))
      (assignment, modelSym)
    }

    def assignModelValue(varName : String, modelSym : Symbol) : (Tree, Symbol) = {
      val valueSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(exprClass.tpe)
      val assignment = VAL(valueSym) === (modelValueFunction APPLY (LIT(varName), ID(modelSym)))
      (assignment, valueSym)
    }

    def assignScalaValue(exprToScalaCastSym : Symbol, typeTree : Tree, modelValueSym : Symbol) : (Tree, Symbol) = {
      val scalaValueSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "scalaValue")).setInfo(typeTree.tpe)
      val assignment = VAL(scalaValueSym) === Apply(TypeApply(Ident(exprToScalaCastSym), List(typeTree)), List(Ident(modelValueSym)))
      (assignment, scalaValueSym)
    }

    /* Declare and initializa a new solver, and invoke it with the predicate designated by `exprSym` */
    def invokeSolver(progSym : Symbol, exprSym : Symbol) : (List[Tree], Symbol) = {
      val solverSym  = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "solver")).setInfo(fairZ3SolverClass.tpe)
      val outcomeSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "outcome")).
        setInfo(definitions.tupleType(List(typeRef(NoPrefix, definitions.OptionClass, List(definitions.BooleanClass.tpe)), typeRef(NoPrefix, mapClass, List(identifierClass.tpe, exprClass.tpe)))))
      val solverDeclaration = VAL(solverSym) === NEW(ID(fairZ3SolverClass), NEW(ID(defaultReporter)))
      val setProgram = (solverSym DOT setProgramFunction) APPLY ID(progSym)
      val invocation = VAL(outcomeSym) === ((solverSym DOT restartAndDecideWithModel) APPLY (ID(exprSym), LIT(false)))

      (List(solverDeclaration, setProgram, invocation), outcomeSym)
    }

    /* Generate the two methods required for converting funcheck expressions to
     * Scala terms, and return the method symbols and method definitions
     * respectively */
    def exprToScalaMethods(owner : Symbol, prog : Program) : ((Symbol, Tree), (Symbol, Tree)) = {
      // `method` is the one that matches expressions and converts them
      // recursively, `castMethod` invokes `method` and casts the results.
      val methodSym     = owner.newMethod(NoPosition, unit.fresh.newName(NoPosition, "exprToScala"))
      val castMethodSym = owner.newMethod(NoPosition, unit.fresh.newName(NoPosition, "exprToScalaCast"))

      val parametricType = castMethodSym.newTypeParameter(NoPosition, unit.fresh.newName(NoPosition, "A"))
      parametricType setInfo (TypeBounds(definitions.NothingClass.typeConstructor, definitions.AnyClass.typeConstructor))

      methodSym      setInfo (MethodType(methodSym     newSyntheticValueParams (List(exprClass.tpe)), definitions.AnyClass.tpe))
      castMethodSym  setInfo (PolyType(List(parametricType), MethodType(castMethodSym newSyntheticValueParams (List(exprClass.tpe)), parametricType.tpe)))

      owner.info.decls.enter(methodSym)
      owner.info.decls.enter(castMethodSym)

      // the following is for the recursive method
      val intSym     = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.IntClass.tpe)
      val booleanSym = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.BooleanClass.tpe)

      val definedCaseClasses : Seq[CaseClassDef] = prog.definedClasses.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])

      val matchExpr = (methodSym ARG 0) MATCH (
        CASE((intLiteralModule) APPLY (intSym BIND WILD()))         ==> ID(intSym) ,
        CASE((booleanLiteralModule) APPLY (booleanSym BIND WILD())) ==> ID(booleanSym) ,
        DEFAULT                                                     ==> THROW(exceptionClass, LIT("Cannot convert FunCheck expression to Scala term"))
      )

      // the following is for the casting method
      val castBody = (methodSym APPLY (castMethodSym ARG 0)) AS (parametricType.tpe)

      ((methodSym, DEF(methodSym) === matchExpr), (castMethodSym, DEF(castMethodSym) === castBody))
    }

    /* Declare a new list variable and generate the code for assigning the
     * result of applying the function on the input list */
     // TODO type of map function cannot be resolved.
    def invokeMap(mapFunSym : Symbol, listSym : Symbol) : (Tree, Symbol) = {
      val newListSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "nl")).setInfo(typeRef(NoPrefix, definitions.ListClass, List(definitions.AnyClass.tpe)))
      val assignment = VAL(newListSym) === ((listSym DOT mapFunction) APPLY ID(listSym))
      // val assignment = VAL(newListSym) === (listSym DOT (TypeApply(ID(mapFunction), List(TypeTree(definitions.AnyClass.tpe)))) APPLY ID(listSym))
      (assignment, newListSym)
    }

    def invokeOutputAssignments(outputVarListSym : Symbol, modelSym : Symbol) : (Tree, Symbol) = {
      val assignmentListSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "as")).setInfo(typeRef(NoPrefix, definitions.ListClass, List(definitions.AnyClass.tpe)))
      val assignment = VAL(assignmentListSym) === (outputAssignmentsFunction APPLY (ID(outputVarListSym), ID(modelSym)))
      (assignment, assignmentListSym)
    }

    def invokeMethod(methodSym : Symbol, argSyms : Symbol*) : Tree = {
      methodSym APPLY (argSyms map (ID(_))).toList
    }
  }
}
