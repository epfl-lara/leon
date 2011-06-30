package cp

import purescala.Trees._
import purescala.TypeTrees.classDefToClassType
import purescala.Definitions._
import purescala.Common.Identifier

import Serialization._

trait CodeGeneration {
  self: CPComponent =>
  import global._
  import CODE._

  private lazy val scalaPackage                   = definitions.ScalaPackage

  private lazy val exceptionClass                 = definitions.getClass("java.lang.Exception")

  private lazy val collectionModule               = definitions.getModule("scala.collection")
  private lazy val immutableModule                = definitions.getModule("scala.collection.immutable")
  private lazy val listMapFunction                = definitions.getMember(definitions.ListClass, "map")
  private lazy val listClassApplyFunction         = definitions.getMember(definitions.ListClass, "apply")
  private lazy val listModuleApplyFunction        = definitions.getMember(definitions.ListModule, "apply")
  private lazy val canBuildFromFunction           = definitions.getMember(definitions.ListModule, "canBuildFrom")

  private lazy val iteratorClass                  = definitions.getClass("scala.collection.Iterator")
  private lazy val iteratorMapFunction            = definitions.getMember(iteratorClass, "map")

  private lazy val setClass                       = definitions.getClass("scala.collection.immutable.Set")
  private lazy val setToSeqFunction               = definitions.getMember(setClass, "toSeq")

  private lazy val seqMapFunction                 = definitions.getMember(definitions.SeqClass, "map")

  private lazy val optionClass                    = definitions.getClass("scala.Option")
  private lazy val optionMapFunction              = definitions.getMember(optionClass, "map")

  private lazy val cpPackage                      = definitions.getModule("cp")

  private lazy val runtimeMethodsModule           = definitions.getModule("cp.RuntimeMethods")
  private lazy val inputVarFunction               = definitions.getMember(runtimeMethodsModule, "inputVar")
  private lazy val skipCounterFunction            = definitions.getMember(runtimeMethodsModule, "skipCounter")
  private lazy val copySettingsFunction           = definitions.getMember(runtimeMethodsModule, "copySettings")
  private lazy val variableFromLFunction          = definitions.getMember(runtimeMethodsModule, "variableFromL")
  private lazy val isSetFunction                  = definitions.getMember(runtimeMethodsModule, "isSet")
  private lazy val toScalaMapFunction             = definitions.getMember(runtimeMethodsModule, "toScalaMap")
  private lazy val toScalaSetFunction             = definitions.getMember(runtimeMethodsModule, "toScalaSet")
  private lazy val toScalaFunctionFunction        = definitions.getMember(runtimeMethodsModule, "toScalaFunction")

  private lazy val converterClass                 = definitions.getClass("cp.Converter")

  private lazy val serializationModule            = definitions.getModule("cp.Serialization")
  private lazy val getProgramFunction             = definitions.getMember(serializationModule, "getProgram")
  private lazy val getInputVarListFunction        = definitions.getMember(serializationModule, "getInputVarList")
  private lazy val serializedClass                = definitions.getClass("cp.Serialization.Serialized")

  private lazy val purescalaPackage               = definitions.getModule("purescala")

  private lazy val definitionsModule              = definitions.getModule("purescala.Definitions")
  private lazy val programClass                   = definitions.getClass("purescala.Definitions.Program")
  private lazy val caseClassDefFunction           = definitions.getMember(programClass, "caseClassDef")
  private lazy val caseClassDefClass              = definitions.getClass("purescala.Definitions.CaseClassDef")
  private lazy val idField                        = definitions.getMember(caseClassDefClass, "id")

  private lazy val commonModule                   = definitions.getModule("purescala.Common")
  private lazy val identifierClass                = definitions.getClass("purescala.Common.Identifier")
  private lazy val nameField                      = definitions.getMember(identifierClass, "name")

  private lazy val treesModule                    = definitions.getModule("purescala.Trees")
  private lazy val exprClass                      = definitions.getClass("purescala.Trees.Expr")
  private lazy val intLiteralModule               = definitions.getModule("purescala.Trees.IntLiteral")
  private lazy val intLiteralClass                = definitions.getClass("purescala.Trees.IntLiteral")
  private lazy val booleanLiteralModule           = definitions.getModule("purescala.Trees.BooleanLiteral")
  private lazy val booleanLiteralClass            = definitions.getClass("purescala.Trees.BooleanLiteral")
  private lazy val caseClassModule                = definitions.getModule("purescala.Trees.CaseClass")
  private lazy val caseClassClass                 = definitions.getClass("purescala.Trees.CaseClass")
  private lazy val andClass                       = definitions.getClass("purescala.Trees.And")
  private lazy val equalsClass                    = definitions.getClass("purescala.Trees.Equals")
  private lazy val finiteSetClass                 = definitions.getClass("purescala.Trees.FiniteSet")
  private lazy val finiteSetModule                = definitions.getModule("purescala.Trees.FiniteSet")
  private lazy val finiteMapClass                 = definitions.getClass("purescala.Trees.FiniteMap")
  private lazy val finiteMapModule                = definitions.getModule("purescala.Trees.FiniteMap")
  private lazy val singletonMapClass              = definitions.getClass("purescala.Trees.SingletonMap")

  private def termModules(arity : Int)            = definitions.getModule("cp.Terms.Term" + arity)

  class CodeGenerator(unit : CompilationUnit, owner : Symbol, defaultPos : Position) {

    private def newSerialized(serialized : Serialized) : Tree = {
      NEW(ID(serializedClass), LIT(serialized.string), LIT(serialized.id))
    }

    def exprSeqToScalaMethod(owner : Symbol, exprToScalaCastSym : Symbol, signature : List[Tree]) : (Tree, Symbol) = {
      val returnType = if (signature.size == 1) signature.head.tpe else definitions.tupleType(signature.map(_.tpe))

      val methodSym = owner.newMethod(NoPosition, unit.fresh.newName("exprSeqToScala"))
      methodSym setInfo (MethodType(methodSym newSyntheticValueParams (List(typeRef(NoPrefix, definitions.SeqClass, List(exprClass.tpe)))), returnType))

      owner.info.decls.enter(methodSym)
      val arg = methodSym ARG 0
      val returnExpressions = (for ((typeTree, idx) <- signature.zipWithIndex) yield {
        val argExpr = ((arg DOT listClassApplyFunction) APPLY LIT(idx)) AS (exprClass.tpe)
        Apply(TypeApply(Ident(exprToScalaCastSym), List(typeTree)), List(argExpr))
      })

      val returnExpr : Tree = if (signature.size == 1) returnExpressions.head else {
        val tupleTypeTree = TypeTree(returnType)
        New(tupleTypeTree,List(returnExpressions))
      }

      (DEF(methodSym) === returnExpr, methodSym)
    }

    /* Generate the two methods required for converting funcheck expressions to
     * Scala terms, and return the method symbols and method definitions
     * respectively */
    def exprToScalaMethods(owner : Symbol, prog : Program) : ((Symbol, Tree), (Symbol, Tree)) = {
      // `method` is the one that matches expressions and converts them
      // recursively, `castMethod` invokes `method` and casts the results.
      val methodSym     = owner.newMethod(NoPosition, unit.fresh.newName("exprToScala"))
      val castMethodSym = owner.newMethod(NoPosition, unit.fresh.newName("exprToScalaCast"))

      // PS: Changed the following for 2.9.0.1 :
      // val parametricType = castMethodSym.newTypeParameter(NoPosition, unit.fresh.newName("A"))
      val parametricType = castMethodSym.newTypeParameter(NoPosition, global.newTypeName("A"))
      parametricType setInfo (TypeBounds(definitions.NothingClass.typeConstructor, definitions.AnyClass.typeConstructor))

      methodSym      setInfo (MethodType(methodSym     newSyntheticValueParams (List(exprClass.tpe)), definitions.AnyClass.tpe))
      castMethodSym  setInfo (PolyType(List(parametricType), MethodType(castMethodSym newSyntheticValueParams (List(exprClass.tpe)), parametricType.tpe)))

      owner.info.decls.enter(methodSym)
      owner.info.decls.enter(castMethodSym)

      // the following is for the recursive method
      val intSym        = methodSym.newValue(NoPosition, unit.fresh.newName("value")).setInfo(definitions.IntClass.tpe)
      val booleanSym    = methodSym.newValue(NoPosition, unit.fresh.newName("value")).setInfo(definitions.BooleanClass.tpe)
      val finiteMapSym  = methodSym.newValue(NoPosition, unit.fresh.newName("map")).setInfo(finiteMapClass.tpe)
      val finiteSetSym  = methodSym.newValue(NoPosition, unit.fresh.newName("set")).setInfo(finiteSetClass.tpe)

      val ccdBinderSym  = methodSym.newValue(NoPosition, unit.fresh.newName("ccd")).setInfo(caseClassDefClass.tpe)
      val argsBinderSym = methodSym.newValue(NoPosition, unit.fresh.newName("args")).setInfo(typeRef(NoPrefix, definitions.SeqClass, List(exprClass.tpe)))

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
                    case _ => scala.sys.error("Cannot generate method using type : " + tpe)
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

      def anonymousFunctionFromMethod(methodSymbol: Symbol, argType: Type): Tree = {
        val anonFunSym = methodSymbol.newValue(NoPosition, nme.ANON_FUN_NAME) setInfo (methodSymbol.tpe)
        val argValue = anonFunSym.newValue(NoPosition, unit.fresh.newName("x")) setInfo (argType)
        val anonFun = Function(
          List(ValDef(argValue, EmptyTree)),
          methodSym APPLY ID(argValue)
        ) setSymbol anonFunSym 
        anonFun
      }

      val matchExpr = (methodSym ARG 0) MATCH ( List(
        CASE((intLiteralModule) APPLY (intSym BIND WILD()))         ==> ID(intSym),
        CASE((booleanLiteralModule) APPLY (booleanSym BIND WILD())) ==> ID(booleanSym),
        CASE(finiteMapSym BIND ((finiteMapModule) APPLY (WILD())))  ==> (toScalaMapFunction APPLY (ID(finiteMapSym), anonymousFunctionFromMethod(methodSym, exprClass.tpe))),
        CASE(finiteSetSym BIND ((finiteSetModule) APPLY (WILD())))  ==> (toScalaSetFunction APPLY (ID(finiteSetSym), anonymousFunctionFromMethod(methodSym, exprClass.tpe)))) :::
        caseClassMatchCases :::
        List(DEFAULT                                                ==> THROW(exceptionClass, LIT("Cannot convert FunCheck expression to Scala term"))) : _*
      )

      // the following is for the casting method
      val castBody = (methodSym APPLY (castMethodSym ARG 0)) AS (parametricType.tpe)

      ((methodSym, DEF(methodSym) === matchExpr), (castMethodSym, DEF(castMethodSym) === castBody))
    }

    /* Generate the method for converting ground Scala terms into funcheck
     * expressions */
    def scalaToExprMethod(owner : Symbol, prog : Program, serializedProg : Serialized) : (Tree, Symbol) = {
      val methodSym = owner.newMethod(NoPosition, unit.fresh.newName("scalaToExpr"))
      methodSym setInfo (MethodType(methodSym newSyntheticValueParams (List(definitions.AnyClass.tpe)), exprClass.tpe))
      owner.info.decls.enter(methodSym)

      val intSym        = methodSym.newValue(NoPosition, unit.fresh.newName("value")).setInfo(definitions.IntClass.tpe)
      val booleanSym    = methodSym.newValue(NoPosition, unit.fresh.newName("value")).setInfo(definitions.BooleanClass.tpe)

      // TODO how to declare this type Set[_] 
      val setType     = typeRef(NoPrefix, setClass, List(WildcardType))
      val setSym     = methodSym.newValue(NoPosition, unit.fresh.newName("value")).setInfo(setType)
      val setSymAlt = methodSym.newValue(NoPosition, unit.fresh.newName("set")).setInfo(definitions.AnyClass.tpe)

      // anonymous function for mapping set to FiniteSet expression
      // val anonFunSym = methodSym.newValue(NoPosition, nme.ANON_FUN_NAME) setInfo (methodSym.tpe)
      // val argValue = anonFunSym.newValue(NoPosition, unit.fresh.newName("x")) setInfo (definitions.AnyClass.tpe)
      // val anonFun = Function(
      //   List(ValDef(argValue, EmptyTree)),
      //   methodSym APPLY ID(argValue)
      // ) setSymbol anonFunSym 

      val definedCaseClasses : Seq[CaseClassDef] = prog.definedClasses.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef])
      val dccSyms = definedCaseClasses map (reverseClassesToClasses(_))

      val caseClassMatchCases = ((definedCaseClasses zip dccSyms) map {
        case (ccd, scalaSym) =>
          /*
          val binderSyms = (ccd.fields.map {
            case VarDecl(id, tpe) =>
              methodSym.newValue(NoPosition, unit.fresh.newName(id.name)).setInfo(definitions.AnyClass.tpe)
          }).toList
          */

          val scalaBinderSym = methodSym.newValue(NoPosition, unit.fresh.newName("cc")).setInfo(scalaSym.tpe)

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
                  (((cpPackage DOT serializationModule DOT getProgramFunction) APPLY (newSerialized(serializedProg))) DOT caseClassDefFunction) APPLY LIT(scalaSym.nameString),
                  (scalaPackage DOT collectionModule DOT immutableModule DOT definitions.ListModule DOT listModuleApplyFunction) APPLY (memberSyms map {
                    case ms => methodSym APPLY (scalaBinderSym DOT ms)
                  })
                )
              )
            )
      }).toList

      val matchExpr = (methodSym ARG 0) MATCH ( List(
        CASE(intSym     BIND Typed(WILD(), TypeTree(definitions.IntClass.tpe)))     ==> NEW(ID(intLiteralClass), ID(intSym)) ,
        CASE(booleanSym BIND Typed(WILD(), TypeTree(definitions.BooleanClass.tpe))) ==> NEW(ID(booleanLiteralClass), ID(booleanSym))
        //(CASE(setSymAlt) IF (isSetFunction APPLY (ID(setSymAlt))))                  ==> NEW(ID(finiteSetClass), 
        /*,
        CASE(setSym     BIND Typed(WILD(), TypeTree(setType)))                      ==> NEW(ID(finiteSetClass), NEW(ID(intLiteralClass), LIT(42)), TypeApply(setSym DOT setToSeqFunction DOT seqMapFunction, List(TypeTree(exprClass.tpe))) APPLY anonFun)*/) :::
        caseClassMatchCases :::
        List(DEFAULT                                                                ==> THROW(exceptionClass, LIT("Cannot convert Scala term to FunCheck expression"))) : _*
      )

      (DEF(methodSym) === matchExpr, methodSym)
    }

    /* Generates list of values that will replace the specified serialized input variables in a constraint */
    def inputVarValues(serializedInputVarList : Serialized, inputVars : Seq[Identifier], lVars : Seq[Identifier], scalaToExprSym : Symbol) : Tree = {
      val inputVarTrees = inputVars.map((iv: Identifier) => scalaToExprSym APPLY variablesToTrees(Variable(iv))).toList
      val lvarConversionTrees = lVars.map((lid: Identifier) => variableFromLFunction APPLY reverseLvarSubsts(Variable(lid))).toList
      (scalaPackage DOT collectionModule DOT immutableModule DOT definitions.ListModule DOT listModuleApplyFunction) APPLY (inputVarTrees ::: lvarConversionTrees)
    }

    def newBaseTerm(exprToScalaSym : Symbol, serializedProg : Serialized, serializedInputVarList : Serialized, serializedOutputVars : Serialized, serializedExpr : Serialized, inputVarValues : Tree, function : Tree, typeTreeList : List[Tree], arity : Int) : Tree = {
      TypeApply(
        Ident(termModules(arity)), typeTreeList) APPLY(
        newConverter(exprToScalaSym),
        newSerialized(serializedProg),
        newSerialized(serializedInputVarList),
        newSerialized(serializedOutputVars),
        newSerialized(serializedExpr),
        inputVarValues,
        function
      )
    }

    def newConverter(exprToScalaSym : Symbol) : Tree = {
      val anonFunSym = owner.newValue(NoPosition, nme.ANON_FUN_NAME) setInfo (exprToScalaSym.tpe)
      val argValue = anonFunSym.newValue(NoPosition, unit.fresh.newName("x")) setInfo (exprClass.tpe)

      val anonFun = Function(
        List(ValDef(argValue, EmptyTree)),
        exprToScalaSym APPLY ID(argValue)
      ) setSymbol anonFunSym 

      NEW(
        ID(converterClass),
        anonFun
      )
    }

    def skipCounter(i : Int) : Tree = {
      (cpPackage DOT runtimeMethodsModule DOT skipCounterFunction) APPLY LIT(i)
    }

    def copySettings(serializedSettings : Serialized) : Tree = {
      (cpPackage DOT runtimeMethodsModule DOT copySettingsFunction) APPLY (newSerialized(serializedSettings))
    }
  }
}
