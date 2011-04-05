package cp

import purescala.Trees._
import purescala.TypeTrees.classDefToClassType
import purescala.Definitions._
import purescala.Common.Identifier

trait CodeGeneration {
  self: CPComponent =>
  import global._
  import CODE._

  private lazy val scalaPackage = definitions.ScalaPackage

  private lazy val exceptionClass = definitions.getClass("java.lang.Exception")

  private lazy val collectionModule = definitions.getModule("scala.collection")
  private lazy val immutableModule =  definitions.getModule("scala.collection.immutable")
  private lazy val listMapFunction = definitions.getMember(definitions.ListClass, "map")
  private lazy val listClassApplyFunction = definitions.getMember(definitions.ListClass, "apply")
  private lazy val listModuleApplyFunction = definitions.getMember(definitions.ListModule, "apply")

  private lazy val mapClass = definitions.getClass("scala.collection.immutable.Map")

  private lazy val cpPackage = definitions.getModule("cp")

  private lazy val callTransformationModule  = definitions.getModule("cp.CallTransformation")
  private lazy val outputAssignmentsFunction = definitions.getMember(callTransformationModule, "outputAssignments")
  private lazy val modelFunction             = definitions.getMember(callTransformationModule, "model")
  private lazy val modelValueFunction        = definitions.getMember(callTransformationModule, "modelValue")
  private lazy val inputVarFunction          = definitions.getMember(callTransformationModule, "inputVar")
  private lazy val skipCounterFunction       = definitions.getMember(callTransformationModule, "skipCounter")

  private lazy val serializationModule      = definitions.getModule("cp.Serialization")
  private lazy val getProgramFunction       = definitions.getMember(serializationModule, "getProgram")
  private lazy val getExprFunction          = definitions.getMember(serializationModule, "getExpr")
  private lazy val getOutputVarListFunction = definitions.getMember(serializationModule, "getOutputVarList")
  private lazy val getInputVarListFunction  = definitions.getMember(serializationModule, "getInputVarList")

  private lazy val purescalaPackage = definitions.getModule("purescala")

  private lazy val definitionsModule    = definitions.getModule("purescala.Definitions")
  private lazy val programClass         = definitions.getClass("purescala.Definitions.Program")
  private lazy val caseClassDefFunction = definitions.getMember(programClass, "caseClassDef")
  private lazy val caseClassDefClass    = definitions.getClass("purescala.Definitions.CaseClassDef")
  private lazy val idField              = definitions.getMember(caseClassDefClass, "id")

  private lazy val commonModule    = definitions.getModule("purescala.Common")
  private lazy val identifierClass = definitions.getClass("purescala.Common.Identifier")
  private lazy val nameField       = definitions.getMember(identifierClass, "name")

  private lazy val treesModule          = definitions.getModule("purescala.Trees")
  private lazy val exprClass            = definitions.getClass("purescala.Trees.Expr")
  private lazy val intLiteralModule     = definitions.getModule("purescala.Trees.IntLiteral")
  private lazy val intLiteralClass      = definitions.getClass("purescala.Trees.IntLiteral")
  private lazy val booleanLiteralModule = definitions.getModule("purescala.Trees.BooleanLiteral")
  private lazy val booleanLiteralClass  = definitions.getClass("purescala.Trees.BooleanLiteral")
  private lazy val caseClassModule      = definitions.getModule("purescala.Trees.CaseClass")
  private lazy val caseClassClass       = definitions.getClass("purescala.Trees.CaseClass")
  private lazy val andClass             = definitions.getClass("purescala.Trees.And")
  private lazy val equalsClass          = definitions.getClass("purescala.Trees.Equals")

  private lazy val fairZ3SolverClass         = definitions.getClass("purescala.FairZ3Solver")
  private lazy val restartAndDecideWithModel = definitions.getMember(fairZ3SolverClass, "restartAndDecideWithModel")
  private lazy val setProgramFunction        = definitions.getMember(fairZ3SolverClass, "setProgram")

  private lazy val defaultReporter = definitions.getClass("purescala.DefaultReporter")

  class CodeGenerator(unit : CompilationUnit, owner : Symbol, defaultPos : Position) {

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
      val intSym        = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.IntClass.tpe)
      val booleanSym    = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.BooleanClass.tpe)

      val ccdBinderSym  = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "ccd")).setInfo(caseClassDefClass.tpe)
      val argsBinderSym = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "args")).setInfo(typeRef(NoPrefix, definitions.SeqClass, List(exprClass.tpe)))

      val definedCaseClasses : Seq[CaseClassDef] = prog.definedClasses.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])
      val dccSyms = definedCaseClasses map (reverseClassesToClasses(_))

      val caseClassMatchCases : List[CaseDef] = ((definedCaseClasses zip dccSyms) map {
        case (ccd, scalaSym) =>
          (CASE(caseClassModule APPLY ((ccdBinderSym BIND WILD()), (argsBinderSym BIND WILD()))) IF ((ccdBinderSym DOT idField DOT nameField).setPos(defaultPos) ANY_== LIT(ccd.id.name).setPos(defaultPos))) ==>
            New(TypeTree(scalaSym.tpe), List({
              (ccd.fields.zipWithIndex map {
                case (VarDecl(id, tpe), idx) =>
                  val typeArg = tpe match {
                    case purescala.TypeTrees.BooleanType => definitions.BooleanClass
                    case purescala.TypeTrees.Int32Type => definitions.IntClass
                    case c : purescala.TypeTrees.ClassType => reverseClassesToClasses(c.classDef)
                    case _ => scala.Predef.error("Cannot generate method using type : " + tpe)
                  }
                  Apply(
                    TypeApply(
                      Ident(castMethodSym), 
                      List(TypeTree(typeArg.tpe))
                    ), 
                    List(
                       // cast hack to make typer happy :(
                       ((argsBinderSym DOT listClassApplyFunction) APPLY LIT(idx)) AS (exprClass.tpe)
                    )
                  )
              }).toList
            }))
      }).toList

      val matchExpr = (methodSym ARG 0) MATCH ( List(
        CASE((intLiteralModule) APPLY (intSym BIND WILD()))         ==> ID(intSym) ,
        CASE((booleanLiteralModule) APPLY (booleanSym BIND WILD())) ==> ID(booleanSym)) :::
        caseClassMatchCases :::
        List(DEFAULT                                                ==> THROW(exceptionClass, LIT("Cannot convert FunCheck expression to Scala term"))) : _*
      )

      // the following is for the casting method
      val castBody = (methodSym APPLY (castMethodSym ARG 0)) AS (parametricType.tpe)

      ((methodSym, DEF(methodSym) === matchExpr), (castMethodSym, DEF(castMethodSym) === castBody))
    }

    /* Generate the method for converting ground Scala terms into funcheck
     * expressions */
    def scalaToExprMethod(owner : Symbol, prog : Program, programFilename : String) : (Tree, Symbol) = {
      val methodSym = owner.newMethod(NoPosition, unit.fresh.newName(NoPosition, "scalaToExpr"))
      methodSym setInfo (MethodType(methodSym newSyntheticValueParams (List(definitions.AnyClass.tpe)), exprClass.tpe))
      owner.info.decls.enter(methodSym)

      val intSym        = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.IntClass.tpe)
      val booleanSym    = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "value")).setInfo(definitions.BooleanClass.tpe)

      val definedCaseClasses : Seq[CaseClassDef] = prog.definedClasses.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])
      val dccSyms = definedCaseClasses map (reverseClassesToClasses(_))

      val caseClassMatchCases = ((definedCaseClasses zip dccSyms) map {
        case (ccd, scalaSym) =>
          /*
          val binderSyms = (ccd.fields.map {
            case VarDecl(id, tpe) =>
              methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, id.name)).setInfo(definitions.AnyClass.tpe)
          }).toList
          */

          val scalaBinderSym = methodSym.newValue(NoPosition, unit.fresh.newName(NoPosition, "cc")).setInfo(scalaSym.tpe)

          val memberSyms = (ccd.fields.map {
            case VarDecl(id, tpe) =>
              scalaSym.info.member(id.name)
          }).toList

          // CASE(scalaSym APPLY (binderSyms map (_ BIND WILD()))) ==>
          CASE(scalaBinderSym BIND Typed(WILD(), TypeTree(scalaSym.tpe))) ==>
            New(
              TypeTree(caseClassClass.tpe),
              List(
                List(
                  (((cpPackage DOT serializationModule DOT getProgramFunction) APPLY LIT(programFilename)) DOT caseClassDefFunction) APPLY LIT(scalaSym.nameString),
                  (scalaPackage DOT collectionModule DOT immutableModule DOT definitions.ListModule DOT listModuleApplyFunction) APPLY (memberSyms map {
                    case ms => methodSym APPLY (scalaBinderSym DOT ms)
                  })
                )
              )
            )
      }).toList

      val matchExpr = (methodSym ARG 0) MATCH ( List(
        CASE(intSym     BIND Typed(WILD(), TypeTree(definitions.IntClass.tpe)))     ==> NEW(ID(intLiteralClass), ID(intSym)) ,
        CASE(booleanSym BIND Typed(WILD(), TypeTree(definitions.BooleanClass.tpe))) ==> NEW(ID(booleanLiteralClass), ID(booleanSym))) :::
        caseClassMatchCases :::
        List(DEFAULT                                                                ==> THROW(exceptionClass, LIT("Cannot convert Scala term to FunCheck expression"))) : _*
      )

      (DEF(methodSym) === matchExpr, methodSym)
    }

    def inputEquality(inputVarListFilename : String, varId : Identifier, scalaToExprSym : Symbol) : Tree = {
      NEW(
        ID(equalsClass),
          // retrieve input variable list and get corresponding variable
        (cpPackage DOT callTransformationModule DOT inputVarFunction) APPLY
          ((cpPackage DOT serializationModule DOT getInputVarListFunction) APPLY LIT(inputVarListFilename), LIT(varId.name)),
        // invoke s2e on var symbol
        scalaToExprSym APPLY ID(reverseVarSubsts(Variable(varId)))
      )
    }

    def assignAndExpr(exprs : Tree*) : (Tree, Symbol) = {
      val andSym = owner.newValue(NoPosition, unit.fresh.newName(NoPosition, "andExpr")).setInfo(exprClass.tpe)
      val statement = VAL(andSym) === NEW(ID(andClass), (scalaPackage DOT collectionModule DOT immutableModule DOT definitions.ListModule DOT listModuleApplyFunction) APPLY (exprs.toList))
      (statement, andSym)
    }

    def skipCounter(progSym : Symbol) : Tree = {
      (cpPackage DOT callTransformationModule DOT skipCounterFunction) APPLY ID(progSym)
    }

  }
}
