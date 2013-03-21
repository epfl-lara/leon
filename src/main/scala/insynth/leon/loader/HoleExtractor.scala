package insynth.leon.loader

import insynth.leon.{ ImmediateExpression, LeonDeclaration }

import leon.purescala.Definitions.{ Program, FunDef }
import leon.purescala.Trees._
import leon.purescala.Extractors._
import leon.purescala.Common.{ Identifier }

class HoleExtractor(program: Program, hole: Hole) {
  
  import DeclarationFactory._
  
  def extractHole: Option[(FunDef, List[LeonDeclaration])] = {
    
    // the list of declarations to be returned
    //var list = scala.collection.mutable.MutableList[Declaration]()
    
    // XXX we currently go through all functions, not efficient!
    var foundHoleCount = 0
    for (
      funDef <-program.definedFunctions;
      if funDef.hasBody;
      val (foundHole, declarations) = scanMethod(funDef.getBody);      
      if foundHole;
      val argDeclarations = funDef.args map { makeArgumentDeclaration(_) }
    ) {
      // hack
      //Globals.holeFunDef = funDef
      
      foundHoleCount+=1
          	
    	return Some((funDef, argDeclarations.toList ++ declarations))
    }
    //assert(foundHoleCount <= 1)
    
    None
    
  }
  
  def scanMethod(functionBody: Expr): (Boolean, Set[LeonDeclaration]) = {
    
    case class LocalPair(foundHole: Boolean, currentSet: Set[Identifier]) {
    	def ++?(pair: Pair[Boolean, Set[Identifier]]): (Boolean, Set[Identifier]) = {
    	  val (foundHoleSec, currentSetSec) = pair
    	  if (foundHole)
    	    (true, currentSet)
    	  else (foundHoleSec, currentSet ++ currentSetSec)
    	}  
    	def +(id: Identifier): (Boolean, Set[Identifier]) = {
    	  (foundHole, currentSet + id)
    	}  
    	def /:\(pair: Pair[Boolean, Set[Identifier]]): (Boolean, Set[Identifier]) = {
    	  if (foundHole)
    	    (foundHole, currentSet)
  	    else
  	      pair
    	}  
    }
	  implicit def localPairCast(pair: Pair[Boolean, Set[Identifier]]) = LocalPair(pair._1, pair._2)
    
	  def allIdentifiers(expr: Expr) : (Boolean, Set[Identifier]) = expr match {
	    case l @ Let(binder, e, b) => allIdentifiers(e) /:\ ( allIdentifiers(b) + binder )
//	    case l @ LetVar(binder, e, b) => allIdentifiers(e) /:\ ( allIdentifiers(b) + binder )
//	    case l @ LetDef(fd, b) =>
//	      allIdentifiers(fd.getBody) /:\ ( allIdentifiers(b) + fd.id )
	    
	    //case block @ Block(exprs, last)	    
	    // NOTE: NAryOperator covers block
	    case n @ NAryOperator(args, _) =>
	      ((false, Set[Identifier]()) /: (args map (allIdentifiers(_)))) {	        
	        case (currentPair, newPair) => currentPair /:\ newPair
	      }
	    case b @ BinaryOperator(a1,a2,_) => allIdentifiers(a1) ++? allIdentifiers(a2)
	    case u @ UnaryOperator(a,_) => allIdentifiers(a)
	    case i @ IfExpr(a1,a2,a3) => allIdentifiers(a1) /:\ allIdentifiers(a2) /:\ allIdentifiers(a3)
	    case m @ MatchExpr(scrut, cses) =>
	      // ??
	      allIdentifiers(scrut) ++?
	      ( (false, Set[Identifier]()) /: ( cses map {
	          cse =>
	        	val rhsResult = allIdentifiers(cse.rhs)
	        	(rhsResult._1, rhsResult._2 ++ cse.pattern.allIdentifiers)
        	})
        ) {        
	        case (currentPair, newPair) => currentPair ++? newPair
	      }
	    case Variable(id) => (false, Set.empty)
	    case h: Hole => (true, Set.empty) 
	    case t: Terminal => (false, Set.empty)
	  }
	  
	  val (foundHole, collectedIdentifiers) = allIdentifiers(functionBody)
	  
	  (
      foundHole,
		  for ( id <- collectedIdentifiers )
		    yield makeDeclaration(
	        ImmediateExpression( id, Variable(id) ), 
	        id.getType
	      )
    )
	  
  }

}