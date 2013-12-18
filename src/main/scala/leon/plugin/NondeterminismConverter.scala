package leon
package plugin

import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import leon.LeonContext
import leon.LeonPhase
import leon.invariant._
import leon.purescala.NonDeterminismExtension

/**
 * TODO: statically enforce that the pre/post conditions do not involve functions 
 * with non-determinism.
 * This restriction may be relaxed later. 
 * However, note that the current implementation does not soundly handle usages of nondet  in the postconditions.
 */
object NondeterminismConverter extends LeonPhase[Program,Program] {
  val name = "Nondeterminism Converter Phase"
  val description = "Handles non-determinism in programs"  

  def run(ctx: LeonContext)(program: Program) : Program = {
                
    // Map from old fundefs to new fundefs
	var funMap = Map[FunDef, FunDef]()
  
	//find functions that use nondet in the body or are transitively called from such functions
	var rootFuncs = Set[FunDef]()
	program.definedFunctions.foreach((fd) => { 
	  if(fd.hasBody && NonDeterminismExtension.hasNondet(fd.body.get)) {
	    rootFuncs += fd
	  } 
	})
	//find all functions that transitively call rootFuncs (here ignore functions called via pre/post conditions)
	val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)
	val callers = program.definedFunctions.foldLeft(Set[FunDef]())((acc, fd) => {
	  if(rootFuncs.exists(cg.transitivelyCalls(fd, _)))
	      acc + fd
	      else acc
	})

    //create new functions.  change a function to a predicate iff it uses nondet or if it transitively calls
	//something that uses nondet    
    for (fd <- program.definedFunctions) {
      
      if (callers.contains(fd)) {   
        //convert the function to a predicate        
        val newres = FreshIdentifier("fres",true).setType(fd.returnType)
        val freshId = FreshIdentifier(fd.id.name, true).setType(BooleanType)
        val newfd = new FunDef(freshId, BooleanType, fd.args :+ VarDecl(newres, fd.returnType))
        funMap += (fd -> newfd)
      } else {
        //here the old and new functiosn are identical
        val freshId = FreshIdentifier(fd.id.name, true).setType(fd.returnType)
        val newfd = new FunDef(freshId, fd.returnType, fd.args)
        funMap += (fd -> newfd)
      }
    }
	//println("FunMap: "+funMap.map((elem) => (elem._1.id, elem._2.id)))

    def mapCalls(ine: Expr): Expr = {
      simplePostTransform((e: Expr) => e match {
        case fi@FunctionInvocation(fd, args) =>
          if (callers.contains(fd)) {
            //return the expression { assume(newfd(args, r)); r} which is realized as let _ = assume(newfd(args, r)) in r,
            //where 'r' is a fresh variable
            val cres = FreshIdentifier("ires",true).setType(fi.getType).toVariable
            //TODO: need to introduce assumes
            val newexpr = Let(FreshIdentifier("dum",true).setType(BooleanType), FunctionInvocation(funMap(fd),args :+ cres), cres)            
            newexpr
          } else {
            val newfi = FunctionInvocation(funMap(fd), args)           
            newfi
          }

        case _ => e
      })(ine)
    } 
    
    for ((from, to) <- funMap) {
      //println("considering function: "+from.id.name)
      to.precondition  = from.precondition.map(mapCalls(_))

      to.postcondition = if (from.hasPostcondition) {
        
        val (fromRes, fromCond) = from.postcondition.get
        val toResId = FreshIdentifier(fromRes.name, true).setType(to.returnType)

        val substsMap = if (callers.contains(from)) {
          //replace fromRes by lastArg of 'to' in fromCond 
          Map[Expr, Expr](fromRes.toVariable -> to.args.last.id.toVariable)
        } else {
          //replace fromRes by toRes in fromCond
          Map[Expr, Expr](fromRes.toVariable -> toResId.toVariable)
        }
        val cond = mapCalls(replace(substsMap, fromCond))
        //the postcondition for nondet functions are conditions that hold only when the result is true
        val toCond = if(callers.contains(from)) Implies(toResId.toVariable, cond)
        			  else  cond

        //important also update the templates here         
        if (FunctionInfoFactory.hasTemplate(from)) {
          val template = mapCalls(replace(substsMap, FunctionInfoFactory.getTemplate(from)))
          val toTemplate = if(callers.contains(from)) Implies(toResId.toVariable, template)
          					else template
          //creating new template          
          FunctionInfoFactory.setTemplate(to, toTemplate)
        }
        Some((toResId, toCond))
        
      } else None

      //make the bodies predicates
      to.body = if (callers.contains(from)) {                
        from.body.map(body => {
          Equals(to.args.last.id.toVariable, mapCalls(body))
        })
      } else{        
        val newbody = from.body.map(mapCalls _)        
        newbody
      } 
    }

    val newDefs = program.mainObject.defs.map {
      case fd: FunDef =>
        funMap(fd)
      case d =>
        d
    }

    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    println("New Prog: \n"+ScalaPrinter.apply(newprog))
    newprog
  }  
}
