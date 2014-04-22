package leon
package invariant.transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import invariant._
import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._
import leon.purescala.ScalaPrinter

/**
 * TODO: is it necessary to create new functions even if it does not use time 
 */
object TimeStepsPhase extends LeonPhase[Program,Program] {
  val name = "Expose Time Phase"
  val description = "Expose runtime steps for each function"  

  def run(ctx: LeonContext)(program: Program) : Program = {
                    
    // Map from old fundefs to new fundefs
	var funMap = Map[FunDef, FunDef]()
  
	//find functions that use time in the postcondition or are transitively called from such functions
	var rootFuncs = Set[FunDef]()
	program.definedFunctions.foreach((fd) => { 
	  if(fd.hasPostcondition 
	      && ExpressionTransformer.isSubExpr(TimeVariable(), fd.postcondition.get._2)) {
	    rootFuncs += fd
	  } 
	  else {
	    val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
        //	    if(FunctionInfoFactory.hasTemplate(fd) 
        //	      && ExpressionTransformer.isSubExpr(TimeVariable(), FunctionInfoFactory.getTemplate(fd))) {
        if (funinfo.isDefined && funinfo.get.hasTemplate
          && ExpressionTransformer.isSubExpr(TimeVariable(), funinfo.get.getTemplate)) {
          rootFuncs += fd
        }	
	  }     
	})
	//find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
	val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)
	val callees = rootFuncs.foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))

    //create new functions.  Augment the return type of a function iff the postcondition uses 'time' 
    // or if the function is transitively called from such a function
    for (fd <- program.definedFunctions) {
      
      if (callees.contains(fd)) {
        val newRetType = TupleType(Seq(fd.returnType, Int32Type))
        val freshId = FreshIdentifier(fd.id.name, false).setType(newRetType)
        val newfd = new FunDef(freshId, fd.tparams, newRetType, fd.params)
        funMap += (fd -> newfd)
      } else {

        //here we need not augment the return types
        val freshId = FreshIdentifier(fd.id.name, false).setType(fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.returnType, fd.params)
        funMap += (fd -> newfd)
      }
    }
	//println("FunMap: "+funMap.map((elem) => (elem._1.id, elem._2.id)))

    def mapCalls(ine: Expr): Expr = {
      simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(tfd, args) =>

          if (callees.contains(tfd.fd)) {
            TupleSelect(FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args), 1)
          } else {
            val fi = FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)           
            fi
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

        val substsMap = if (callees.contains(from)) {
          //replace fromRes by toRes._1 in fromCond and time by toRes._2 in  fromCond
          Map[Expr, Expr](fromRes.toVariable -> TupleSelect(toResId.toVariable, 1), TimeVariable() -> TupleSelect(toResId.toVariable, 2))
        } else {
          //replace fromRes by toRes in fromCond
          Map[Expr, Expr](fromRes.toVariable -> toResId.toVariable)
        }
        val toCond = mapCalls(replace(substsMap, fromCond))

        //important also update the function info here
        val frominfo = FunctionInfoFactory.getFunctionInfo(from)
        if (frominfo.isDefined) {
          val transfunc = (e: Expr) => mapCalls(replace(substsMap, e))
          FunctionInfoFactory.createFunctionInfo(to, transfunc, frominfo.get)
        }          
        //update the timeexpr of toinfo
        if (substsMap.contains(TimeVariable())) {
          val toinfo = FunctionInfoFactory.getOrMakeInfo(to)
          toinfo.setTimeexpr(substsMap(TimeVariable()))
        }

        //          val toTemplate = mapCalls(replace(substsMap, FunctionInfoFactory.getTemplate(from)))
        //          //creating new template                     
        //          FunctionInfoFactory.setTemplate(to, toTemplate,
        //              if(substsMap.contains(TimeVariable())) 
        //                Some(substsMap(TimeVariable()))            
        //              else None)          
        Some((toResId, toCond))
        
      } else None

      //instrument the bodies of all 'callees' only for tracking time
      to.body = if (callees.contains(from)) {
        from.body.map(new ExposeTimes(ctx, getCostModel, funMap).apply _)
      } else{        
        val newbody = from.body.map(mapCalls _)        
        newbody
      } 
      //println("Fun: "+to)
      
      //copy annotations
      from.annotations.foreach((str) => {       
        to.addAnnotation(str)
      })      
    }
    
    val newprog = Util.copyProgram(program, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => funMap(fd)
      case d => d
    })    
//    /println("After Time Instrumentation: \n"+ScalaPrinter.apply(newprog))
    
    //print all the templates
    /*newprog.definedFunctions.foreach((fd) => 
      if(FunctionInfoFactory.hasTemplate(fd))
        println("Function: "+fd.id+" template --> "+FunctionInfoFactory.getTemplate(fd))
        )*/
    newprog
  }
  
  abstract class CostModel {
    def costOf(e: Expr): Int
    def costOfExpr(e: Expr) = IntLiteral(costOf(e))
  }

  def getCostModel: CostModel = {
    // STEP 2: Create a simple cost model and use it here a simple cost model
     new CostModel{
       override def costOf(e: Expr) : Int =  {
         e match {
           case FunctionInvocation(fd,args) => 1           
           case t: Terminal => 0
           case _ => 1           
         }
       }               
     }
  }

  class ExposeTimes(ctx: LeonContext, cm: CostModel, funMap : Map[FunDef,FunDef]) {

    // Returned Expr is always an expr of type tuple (Expr, Int)
    def tupleify(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr): Expr = {
        // When called for:
        // Op(n1,n2,n3)
        // e      = Op(n1,n2,n3)
        // subs   = Seq(n1,n2,n3)
        // recons = { Seq(newn1,newn2,newn3) => Op(newn1, newn2, newn3) }
        //
        // This transformation should return, informally:
        //
        // LetTuple((e1,t1), transform(n1),
        //   LetTuple((e2,t2), transform(n2),
        //    ...
        //      Tuple(recons(e1, e2, ...), t1 + t2 + ... costOfExpr(Op)
        //    ...
        //   )
        // )
        //
        // You will have to handle FunctionInvocation specially here!
        tupleifyRecur(e,subs,recons,List[Identifier](),List[Identifier]())
    }
    
       
    def tupleifyRecur(e: Expr, subs: Seq[Expr], recons: Seq[Expr] => Expr, resIds: List[Identifier], timeIds: List[Identifier]) : Expr = {      
    //note: subs.size should be zero if e is a terminal
      if(subs.size == 0)
      {
        //base case (handle terminals and function invocation separately)
        e match {
          case t : Terminal => Tuple(Seq(recons(Seq()), getCostModel.costOfExpr(e)))
          
          case f@FunctionInvocation(tfd,args) => {            
            val newFunInv = FunctionInvocation(TypedFunDef(funMap(tfd.fd),tfd.tps),resIds.map(Variable(_)))
            
            //create a variables to store the result of function invocation
            val resvar = FreshIdentifier("e", true).setType(e.getType)
            val timevar = FreshIdentifier("t", true).setType(Int32Type)            
            
            val costofOp = Plus(getCostModel.costOfExpr(e),Variable(timevar))
            val timePart =
              timeIds.foldLeft(costofOp: Expr)((g: Expr, t: Identifier) => Plus(Variable(t), g))            
            val baseExpr = Tuple(Seq(Variable(resvar), timePart))
                                    
            LetTuple(Seq(resvar,timevar),newFunInv,baseExpr)
          }
          
          case _ => {
            val exprPart = recons(resIds.map(Variable(_)): Seq[Expr])
            val costofOp = getCostModel.costOfExpr(e)
            val timePart =
              timeIds.foldLeft(costofOp: Expr)((g: Expr, t: Identifier) => Plus(Variable(t), g))
            Tuple(Seq(exprPart, timePart))
          }
        }    	
      }
      else
      {
        //recursion step
        val currentElem = subs.head
        val resvar = FreshIdentifier("e", true).setType(currentElem.getType)
        val timevar = FreshIdentifier("t", true).setType(Int32Type)
                
        ///recursively call the method on subs.tail
        val recRes = tupleifyRecur(e,subs.tail,recons,resIds :+ resvar, timeIds :+ timevar)
        
        //transform the current element (handle function invocation separately)        
        val newCurrExpr = transform(subs.head)
        /*subs.head match {
          case FunctionInvocation(fd,args) => {
            //use the new function definition in funmap
            val newfun = FunctionInvocation(funMap(fd),args)
            //transform the function
            transform(newfun)
          } 
          case _ => transform(subs.head)
        }*/
        
        //create the new expression for the current recursion step
        val newexpr = LetTuple(Seq(resvar, timevar ),newCurrExpr,recRes)
        newexpr
      }      
    }

    //TODO: need to handle Assume 
    def transform(e: Expr): Expr = e match {    
      case Let(i, v, b) =>
        val ir = FreshIdentifier("ir", true).setType(v.getType)
        val it = FreshIdentifier("it", true).setType(Int32Type)
        val r = FreshIdentifier("r", true).setType(e.getType)
        val t = FreshIdentifier("t", true).setType(Int32Type)

        LetTuple(Seq(ir, it), transform(v),
          LetTuple(Seq(r,t), replace(Map(Variable(i) -> Variable(ir)), transform(b)),
            Tuple(Seq(Variable(r), Plus(Variable(t), Plus(Variable(it), cm.costOfExpr(e)))))
          )
        )
      
      case LetTuple(ids, v, b) =>
        val ir = FreshIdentifier("ir", true).setType(v.getType)
        val it = FreshIdentifier("it", true).setType(Int32Type)
        val r = FreshIdentifier("r", true).setType(e.getType)
        val t = FreshIdentifier("t", true).setType(Int32Type)
        //TODO: reusing the same 'ids' is it safe ??
        LetTuple(Seq(ir, it), transform(v),
         LetTuple(ids, ir.toVariable,
          LetTuple(Seq(r,t), transform(b),
            Tuple(Seq(Variable(r), Plus(Variable(t), Plus(Variable(it), cm.costOfExpr(e)))))
            )
          )
        )

      case IfExpr(cond, then, elze) =>{
        // You need to handle this case specifically and differently
        
        //create new variables that capture the result of the condition
        val rescond = FreshIdentifier("e", true).setType(cond.getType)
        val timecond = FreshIdentifier("t", true).setType(Int32Type)
        
        //transform the then branch        
        val resthen = FreshIdentifier("e", true).setType(then.getType)
        val timethen = FreshIdentifier("t", true).setType(Int32Type)
        val newthen = LetTuple(Seq(resthen,timethen), transform(then), 
            Tuple(Seq(Variable(resthen),Plus(Variable(timecond),Variable(timethen)))))
                
        //similarly transform the else branch 
        val reselse = FreshIdentifier("e", true).setType(elze.getType)
        val timelse = FreshIdentifier("t", true).setType(Int32Type)
        val newelse = LetTuple(Seq(reselse,timelse), transform(elze), 
            Tuple(Seq(Variable(reselse),Plus(Variable(timecond),Variable(timelse)))))
                
        //create a final expression
        LetTuple(Seq(rescond,timecond),transform(cond), IfExpr(Variable(rescond),newthen,newelse))                
      }
        
      // For all other operations, we go through a common tupleifier.
      case n @ NAryOperator(ss, recons) =>
        tupleify(e, ss, recons)

      case b @ BinaryOperator(s1, s2, recons) =>
        tupleify(e, Seq(s1, s2), { case Seq(s1, s2) => recons(s1, s2) })

      case u @ UnaryOperator(s, recons) =>
        tupleify(e, Seq(s), { case Seq(s) => recons(s) })

      case t: Terminal =>
        tupleify(e, Seq(), { case Seq() => t })
    }


    def apply(e: Expr): Expr = {
      //lift all expressions that are used in matches to before matches.
      val newe =  liftExprInMatch(e)
      // Removes pattern matching by translating to equivalent if-then-else      
      val input  = matchToIfThenElse(newe)
      
      // For debugging purposes      
      /*println("#"*80)
      println("BEFORE:")
      println(input)*/
            
      // Apply transformations
      val res    = transform(input)      
      val simple = simplifyArithmetic(simplifyLets(res))

      // For debugging purposes            
      /*println("-"*80)
      println("AFTER:")      
      println(simple)*/
      simple
    }
    
    def liftExprInMatch(ine: Expr) : Expr = {
      simplePostTransform((e: Expr) => e match {
        case MatchExpr(strut, cases) => strut match {
          case t : Terminal => e
          case _ => {
            val freshid = FreshIdentifier("m",true).setType(strut.getType)
            Let(freshid, strut, MatchExpr(freshid.toVariable, cases))
          }
        } 
        case _ => e        
      })(ine)
    }
  }
}
