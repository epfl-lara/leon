package insynth.testutil

import insynth.leon.{ LeonQueryBuilder => QueryBuilder, _ }
import insynth.reconstruction.stream._

import leon.purescala.Definitions.{ FunDef, VarDecl, Program, ObjectDef }
import leon.purescala.Common.{ FreshIdentifier }
import leon.purescala.TypeTrees._
import leon.purescala.Trees.{ Variable => _, _ }

object CommonLambda {

  implicit val leonToDomainType = DomainTypeTransformer(_: TypeTree)

  import CommonDeclarations._
  import CommonProofTrees._
      
  val booleanIdentifier = Identifier(BooleanType, booleanDeclaration)
  
  def constructBooleanToIntIntermediateLambda = {
    val query = new QueryBuilder(Int32Type)

    val functionApplication =
      Application(
        functionIntToIntType,
        List(
          Identifier(functionBoolToIntType, functionBoolToIntDeclaration),
          booleanIdentifier))

    val intermediateTree =
      Application(
        query.leonType,
        List(
          Identifier(query.leonType, query.getQuery.getDeclaration),
          functionApplication))

    List(intermediateTree)
  }
  
  def constructIntToIntIntermediateFirstLambda(x: Int) = {
    val query = new QueryBuilder(Int32Type)

    val functionApplication =
      Application(
        functionIntToIntType,
        List(
          Identifier(functionIntToIntType, functionIntToIntDeclaration),
          Identifier(Int32Type, intDeclaration)))

    val (_, listOfApplication) =
      (((Identifier(Int32Type, intDeclaration), Nil): (Node, List[Node])) /: (1 to x)) {
      	case ((nextArg, list), _) =>
		      val app =	Application(
		        functionIntToIntType,
		        List(Identifier(functionIntToIntType, functionIntToIntDeclaration),
		          nextArg))
		          
          (app, list :+ app)
    	}
    
    for (app <- listOfApplication) yield 
    	Application(
        query.leonType,
        List(
          Identifier(query.leonType, query.getQuery.getDeclaration),
          app))    
  }    
  
  def constructIntAndBoolToIntIntermediateLambda(x: Int) = {
    val query = new QueryBuilder(Int32Type)

    val functionApplicationBoolean =
      Application(
        functionBoolToIntType,
        List(
          Identifier(functionBoolToIntType, functionBoolToIntDeclaration),
          booleanIdentifier))
          
    val functionApplication =
      Application(
        functionIntToIntType,
        List(
          Identifier(functionIntToIntType, functionIntToIntDeclaration),
          Identifier(Int32Type, intDeclaration)))

    val (listOfApplication, _) =
      (((Nil, List(Identifier(Int32Type, intDeclaration), functionApplicationBoolean)): (List[Node], List[Node])) /: (1 to x)) {
      	case ((list, args), _) =>
		      val listAddition =
		        for (arg <- args) yield
			        Application(functionIntToIntType,
		        		List(Identifier(functionIntToIntType, functionIntToIntDeclaration), arg))
		          
          (list ++ listAddition, listAddition)
    	}
    
    for (app <- listOfApplication) yield 
    	Application(
        query.leonType,
        List(
          Identifier(query.leonType, query.getQuery.getDeclaration),
          app))    
  }  
  
  def constructThreeParFunctionIntermediateLambda(x: Int) = {
    val query = new QueryBuilder(Int32Type)

    val listOfApplication =
      ((List(Identifier(Int32Type, intDeclaration), Identifier(Int32Type, intDeclaration)): List[Node]) /: (1 to x)) {
      	case (list, _) =>
		      val listAddition =
		        (for (arg <- list.combinations(2)) yield
			        Application(
					      threeParFunctionType,
					      List(
					        Identifier(threeParFunctionType, threeParFunctionDeclaration),
					        arg(0),
					        arg(1),
					        booleanIdentifier         
					      )
					    )) ++		      	
		        (for (arg <- list.combinations(2)) yield
			        Application(
					      threeParFunctionType,
					      List(
					        Identifier(threeParFunctionType, threeParFunctionDeclaration),
					        arg(1),
					        arg(0),
					        booleanIdentifier         
					      )
					    ))  ++		      	
		        (for (arg <- list) yield
			        Application(
					      threeParFunctionType,
					      List(
					        Identifier(threeParFunctionType, threeParFunctionDeclaration),
					        arg, arg,
					        booleanIdentifier         
					      )
					    ))				    
		          
          (list ++ listAddition).distinct
    	}
    
    for (app <- listOfApplication.distinct) yield 
    	Application(
        query.leonType,
        List(
          Identifier(query.leonType, query.getQuery.getDeclaration),
          app))
  }
  
  // TODO do if we need abstraction (high-order functions)
//  def constructFunctionIntToIntIntermediateLambda = {
//    val query = new QueryBuilder(FunctionType(List(Int32Type), Int32Type))
//
//    val functionApplicationBoolean =
//      Application(
//        functionBoolToIntType,
//        List(
//          Set(Identifier(functionIntToIntType, functionBoolToIntDeclaration)),
//          Set(booleanIdentifier)))
//          
//    val functionApplication =
//      Application(
//        functionIntToIntType,
//        List(
//          Set(Identifier(functionIntToIntType, functionIntToIntDeclaration)),
//          Set(Variable(Int32Type, "freshInt"), functionApplicationBoolean)))
//
//    functionApplication.recursiveParams = List(Set(functionApplication))
//	
//		val abstraction = Abstraction(functionIntToIntType,
//	    List(Variable(Int32Type, "var_1")), Set(functionApplicationBoolean, functionApplication))
//
//    val intermediateTree =
//      Application(
//        query.leonType,
//        List(
//          Set(Identifier(query.leonType, query.getQuery.getDeclaration)),
//          Set(abstraction)))
//
//    intermediateTree
//  }

}