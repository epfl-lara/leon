package insynth.leon.loader

import insynth.leon.{ LeonDeclaration => Declaration, NaryReconstructionExpression, ImmediateExpression, UnaryReconstructionExpression }
import insynth.structures.{ SuccinctType => InSynthType }
import insynth.interfaces.Loader
import insynth.util.logging.HasLogger

import leon.purescala.Definitions.{ Program, FunDef }
import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Trees.{ Hole, Expr, FunctionInvocation, _ }
import leon.purescala.Common.{ Identifier }
import leon.purescala.Definitions.{ AbstractClassDef, CaseClassDef, ClassTypeDef }

case class LeonLoader(program: Program, hole: Hole,
  variables: List[Identifier], loadArithmeticOps: Boolean = true) extends Loader with HasLogger {  
  //var temporaryDesiredType: LeonType = Int32Type
  
  lazy val classMap: Map[Identifier, ClassType] = extractClasses
  
  lazy val directSubclassesMap: Map[ClassType, Set[ClassType]] = initializeSubclassesMap(program)
  
  // arguments + all found variables in the hole function
  lazy val variableDeclarations: Seq[Declaration] = variables.map(DeclarationFactory.makeArgumentDeclaration(_))
  
  //lazy val holeDef = initResults._3
  
  lazy val initResults = init
  
  import DeclarationFactory._
        
  def load: List[Declaration] = initResults
  
  private def init = {      

    // the list of declarations to be returned
    var list = scala.collection.mutable.MutableList[Declaration]()
            
    /* add declarations to builder */
          
    // add function declarations
    for( funDef@FunDef(id, returnType, args, _, _, _) <- program.definedFunctions ) {
      val leonFunctionType = FunctionType(args map { _.tpe } toList, returnType)
              
      val newDeclaration = makeDeclaration(
        NaryReconstructionExpression( id, { args: List[Expr] => FunctionInvocation(funDef, args) } ), 
        leonFunctionType
      )        
      
      list += newDeclaration        
      fine("Leon loader added declaration: " + newDeclaration)        
    }
    
    // add predefs and literals
    list ++= PreLoader(loadArithmeticOps)
    
    list ++= extractInheritances
    
    list ++= extractCaseClasses
    
    list ++= extractFields
    
    list ++= extractClassDependentDeclarations
    
    list ++= variableDeclarations
    
    for (variable <- variables; variableType = variable.getType) variableType match {
      case variableClassType: CaseClassType => variableClassType.classDef match {
	    case cas@CaseClassDef(id, parent, fields) =>
	      fine("adding fields of variable " + variable)
            for (field <- fields)
	          list += makeDeclaration(
		        ImmediateExpression( "Field(" + cas + "." + field.id + ")",
	            CaseClassSelector(cas, variable.toVariable, field.id) ),
	            field.id.getType
    		  )
	    case _ =>
  		}
      case _ =>
    }
    
    list.toList
    
    // no need for doing this (we will have everything from the synthesis problem context)
//    new HoleExtractor(program, hole).extractHole match {
//      case Some((holeDef, decls)) =>
//        list ++= decls
//                  
//        (list.toList, decls, holeDef)
//      case _ =>
//        throw new RuntimeException("Hole extractor problem")
//    }     
  }
    
  def initializeSubclassesMap(program: Program) = {  
    val seqOfPairs = for (classDef <- program.definedClasses)
    	yield classDef match {
    		case caseClassDef: CaseClassDef =>
    		  val caseClassType = classMap(classDef.id)
    		  ( caseClassType, Set[ClassType]( /*caseClassType*/ ) )
    		case absClassDef: AbstractClassDef =>
    		  val childrenTypes = for (child <- absClassDef.knownChildren)
    		    yield classMap(child.id)
    		  ( classMap(absClassDef.id), childrenTypes.toSet )
    	}
    
    seqOfPairs.toMap
  }
    
  def extractClasses: Map[Identifier, ClassType] = {    
    (
      for (classDef <- program.definedClasses)
	    	yield classDef match {
	    		case caseClassDef: CaseClassDef => ( classDef.id, CaseClassType(caseClassDef) )
	    		case absClassDef: AbstractClassDef => ( absClassDef.id, AbstractClassType(absClassDef) )
	    	}
    ) toMap
  }
  
  // TODO add anyref to all and all to bottom ???
  def extractInheritances: Seq[Declaration] = {
    
    def extractInheritancesRec(classDef: ClassTypeDef): List[Declaration] = 
      classDef match {
        case abs: AbstractClassDef =>
          Nil ++ 
          (
            for (child <- abs.knownChildren)
            	yield makeInheritance(
          	    classMap(child.id), classMap(abs.id)
        	    )
          ) ++ (
            for (child <- abs.knownChildren)
            	yield extractInheritancesRec(child)
          ).flatten
        case _ =>
          Nil
    	}
    
//    (for (classHierarchyRoot <- program.classHierarchyRoots)
//    	yield extractInheritancesRec(classHierarchyRoot)).flatten.toList
    
    for (classHierarchyRoot <- program.classHierarchyRoots;
    			inheritance <- extractInheritancesRec(classHierarchyRoot))
    	yield inheritance
  }

  def extractFields(classDef: ClassTypeDef) = classDef match {
    case abs: AbstractClassDef =>
      // this case does not seem to work
      //abs.fields
      Seq.empty
    case cas: CaseClassDef =>
      for (field <- cas.fields)
        yield makeDeclaration(
        UnaryReconstructionExpression("Field(" + cas + "." + field.id + ")", { CaseClassSelector(cas, _: Expr, field.id) }),
        FunctionType(List(classMap(cas.id)), field.id.getType))
  }
  
  def extractFields: Seq[Declaration] = {
    for (classDef <- program.definedClasses;
    		decl <- extractFields(classDef))
    	yield decl
  }
      
  def extractCaseClasses: Seq[Declaration] = {    
    for (caseClassDef@CaseClassDef(id, parent, fields) <- program.definedClasses)
    	yield fields match {
      	case Nil => makeDeclaration(
	        ImmediateExpression( "Cst(" + id + ")", { CaseClass(caseClassDef, Nil) } ), 
	        classMap(id)
	      )
      	case _ => makeDeclaration(
	        NaryReconstructionExpression( "Cst(" + id + ")", { CaseClass(caseClassDef, _: List[Expr]) } ), 
	        FunctionType(fields map { _.id.getType } toList, classMap(id))
	      )
    	}
  }
  
  def extractClassDependentDeclarations: Seq[Declaration] = {
//    def getClassDef(id: Identifier): CaseClassDef = {
//      program.caseClassDef(id.name)
//      program.definedClasses.find( _.id == `id` ) match {
//        case Some(classDef) => classDef
//        case _ => throw new RuntimeException
//      }
//    }
    
    for ( classDef@CaseClassDef(_, _, _) <- program.definedClasses filter { _.isInstanceOf[CaseClassDef] }; 
    			if classDef.hasParent)
      yield makeDeclaration(
        UnaryReconstructionExpression( "isInstance[" + classDef.id + "]", { CaseClassInstanceOf(classDef, _: Expr) 
        	} ), 
        FunctionType(List(classMap(classDef.parent.get.id)), BooleanType)
      )
  }
  
  // XXX does not care about hiding, does not see function arguments
  
//  def loadLocals(functionBody: Expr, hole: Expr): Set[Declaration] = {
//    scanMethod(functionBody, hole)._2
//  }
  
}

// old load function
//  def load(program: Program, hole: Hole): List[Declaration] = {
//    initializeClassMap(program)
//    
//    var list: scala.collection.mutable.LinkedList[Declaration] = scala.collection.mutable.LinkedList()
//    
//    /* add declarations to builder */
//          
//    // add function declarations
//    for( funDef@FunDef(id, returnType, args, _, _, _) <- program.definedFunctions ) {
//      val leonFunctionType = FunctionType(args map { _.tpe } toList, returnType)
//              
//      val newDeclaration = makeDeclaration(
//        NaryReconstructionExpression( id, { args: List[Expr] => FunctionInvocation(funDef, args) } ), 
//        leonFunctionType
//      )        
//      
//      list :+= newDeclaration              
//    }
//    
//    // add predefs and literals
//    list ++= PreLoader()
//    
//    list ++= extractInheritances(program)
//    
//    list ++= extractCaseClasses(program)
////    
////    builder.addDeclarations( extractClassDependentDeclarations(program) )
//    
//    // XXX we currently go through all functions, not efficient!
//    var foundHoleCount = 0
//    for (
//      funDef <-program.definedFunctions;
//      if funDef.hasBody;
//      val (foundHole, declarations) = scanMethod(funDef.getBody, hole);      
//      if foundHole;
//      val argDeclarations = funDef.args map { makeArgumentDeclaration(_) }
//    ) {
//      // hack
//      Globals.holeFunDef = funDef      
//      foundHoleCount+=1
//      
//    	list ++= declarations.toList
//    	list ++= argDeclarations
//    }
//    assert(foundHoleCount <= 1)
//    
//    list toList
//  }