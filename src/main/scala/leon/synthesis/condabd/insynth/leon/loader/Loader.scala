/* Copyright 2009-2014 EPFL, Lausanne */

package leon.synthesis.condabd.insynth.leon.loader

import leon.synthesis.condabd.insynth.leon.{ LeonDeclaration => Declaration, NaryReconstructionExpression, ImmediateExpression, UnaryReconstructionExpression }
import insynth.structures.{ SuccinctType => InSynthType }
import insynth.load.Loader
import insynth.util.logging.HasLogger

import leon.purescala.Definitions.{ Program, FunDef }
import leon.purescala.TypeTrees.{ TypeTree => LeonType, _ }
import leon.purescala.Trees.{ Expr, FunctionInvocation, _ }
import leon.purescala.Common.{ Identifier }
import leon.purescala.Definitions.{ AbstractClassDef, CaseClassDef, ClassDef }

// enable postfix operations
import scala.language.postfixOps

case class LeonLoader(program: Program, variables: List[Identifier], loadArithmeticOps: Boolean = true)
	extends Loader with HasLogger {  
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
    for( funDef <- program.definedFunctions ) {
      val tfd = funDef.typed(funDef.tparams.map(_.tp))

      val leonFunctionType = tfd.functionType
              
      val newDeclaration = makeDeclaration(
        NaryReconstructionExpression(tfd.fd.id, { args: List[Expr] => FunctionInvocation(tfd, args) } ), 
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
	    case cas @ CaseClassDef(id, tparams, parent, isObj) =>
	      fine("adding fields of variable " + variable)
            for (field <- cas.fields)
	          list += makeDeclaration(
		        ImmediateExpression( field.id.name ,
	            CaseClassSelector(CaseClassType(cas, tparams.map(_.tp)), variable.toVariable, field.id) ),
	            field.id.getType
    		  )
	    case _ =>
  		}
      case _ =>
    }
    
    list.toList   
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
	    		case ccd: CaseClassDef => ( ccd.id, CaseClassType(ccd, ccd.tparams.map(_.tp)) )
	    		case acd: AbstractClassDef => ( acd.id, AbstractClassType(acd, acd.tparams.map(_.tp)) )
	    	}
    ) toMap
  }
  
  // TODO add anyref to all and all to bottom ???
  def extractInheritances: Seq[Declaration] = {
    
    def extractInheritancesRec(classDef: ClassDef): List[Declaration] = 
      classDef match {
        case abs: AbstractClassDef =>
          Nil ++ 
          (
            for (child <- abs.knownChildren)
            	yield makeInheritance(
          	    classMap(child.id), classMap(abs.id)
        	    )
          ) ++ (
            for (child <-abs.knownChildren)
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

  def extractFields(classDef: ClassDef) = classDef match {
    case abs: AbstractClassDef =>
      // this case does not seem to work
      //abs.fields
      Seq.empty
    case cas: CaseClassDef =>
      val cct = CaseClassType(cas, cas.tparams.map(_.tp))
      for (field <- cas.fields)
        yield makeDeclaration(
        UnaryReconstructionExpression(field.id.name, { CaseClassSelector(cct, _: Expr, field.id) }),
        FunctionType(List(classMap(cas.id)), field.id.getType))
  }
  
  def extractFields: Seq[Declaration] = {
    for (classDef <- program.definedClasses;
    		decl <- extractFields(classDef))
    	yield decl
  }
      
  def extractCaseClasses: Seq[Declaration] = {    
    for (caseClassDef @ CaseClassDef(id, tparams, parent, isObj) <- program.definedClasses)
    	yield caseClassDef.fields match {
      	case Nil => makeDeclaration(
	        ImmediateExpression( id.name, { CaseClass(CaseClassType(caseClassDef, caseClassDef.tparams.map(_.tp)), Nil) } ), 
	        classMap(id)
	      )
      	case fields => makeDeclaration(
	        NaryReconstructionExpression( id.name , { CaseClass(CaseClassType(caseClassDef, caseClassDef.tparams.map(_.tp)), _: List[Expr]) } ), 
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
    
for ( classDef <- program.definedClasses collect { case ccd: CaseClassDef => ccd }; 
    			if classDef.hasParent)
      yield makeDeclaration(
        UnaryReconstructionExpression( "isInstance[" + classDef.id + "]", { CaseClassInstanceOf(CaseClassType(classDef, classDef.tparams.map(_.tp)), _: Expr) 
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
//      val argDeclarations = funDef.params map { makeArgumentDeclaration(_) }
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
