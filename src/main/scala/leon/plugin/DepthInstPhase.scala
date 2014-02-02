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

/**
 * TODO: is it necessary to create new functions even if it does not use depth 
 */
object DepthInstPhase extends LeonPhase[Program,Program] {
  val name = "Expose Depth Phase"
  val description = "Expose depth of a function"  

  def maxFun = {
    val xid = FreshIdentifier("x").setType(Int32Type)
    val yid = FreshIdentifier("y").setType(Int32Type)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val fd = new FunDef(FreshIdentifier("max", false), Int32Type, args.map((arg) => VarDecl(arg, arg.getType)))
    //add a body    
    fd.body = Some(IfExpr(GreaterEquals(varx, vary), varx, vary))
    fd
  }
  
  def run(ctx: LeonContext)(program: Program) : Program = {
                
    // Map from old fundefs to new fundefs
	var funMap = Map[FunDef, FunDef]()
  
	//find functions that use depth in the postcondition or are transitively called from such functions
	var rootFuncs = Set[FunDef]()
	program.definedFunctions.foreach((fd) => { 
	  if(fd.hasPostcondition 
	      && ExpressionTransformer.isSubExpr(DepthVariable(), fd.postcondition.get._2)) {
	    rootFuncs += fd
	  } 
	  else if(FunctionInfoFactory.hasTemplate(fd) 
	      && ExpressionTransformer.isSubExpr(DepthVariable(), FunctionInfoFactory.getTemplate(fd))) {
	    rootFuncs += fd
	  }	    
	})
	//find all functions transitively called from rootFuncs (here ignore functions called via pre/post conditions)
	val cg = CallGraphUtil.constructCallGraph(program, onlyBody = true)
	val callees = rootFuncs.foldLeft(Set[FunDef]())((acc, fd) => acc ++ cg.transitiveCallees(fd))

    //create new functions.  Augment the return type of a function iff the postcondition uses 'depth' 
    // or if the function is transitively called from such a function
    for (fd <- program.definedFunctions) {
      
      if (callees.contains(fd)) {
        val newRetType = TupleType(Seq(fd.returnType, Int32Type))
        val freshId = FreshIdentifier(fd.id.name, false).setType(newRetType)
        val newfd = new FunDef(freshId, newRetType, fd.args)
        funMap += (fd -> newfd)
      } else {
        //here we need not augment the return types
        val freshId = FreshIdentifier(fd.id.name, false).setType(fd.returnType)
        val newfd = new FunDef(freshId, fd.returnType, fd.args)
        funMap += (fd -> newfd)
      }
    }
	//println("FunMap: "+funMap.map((elem) => (elem._1.id, elem._2.id)))

    def mapCalls(ine: Expr): Expr = {
      simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(fd, args) =>
          if (callees.contains(fd)) {
            TupleSelect(FunctionInvocation(funMap(fd), args), 1)
          } else {
            val fi = FunctionInvocation(funMap(fd), args)           
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
        val toResId = FreshIdentifier(fromRes.name, false).setType(to.returnType)

        val substsMap = if (callees.contains(from)) {
          //replace fromRes by toRes._1 in fromCond and time by toRes._2 in  fromCond
          Map[Expr, Expr](fromRes.toVariable -> TupleSelect(toResId.toVariable, 1), DepthVariable() -> TupleSelect(toResId.toVariable, 2))
        } else {
          //replace fromRes by toRes in fromCond
          Map[Expr, Expr](fromRes.toVariable -> toResId.toVariable)
        }
        val toCond = mapCalls(replace(substsMap, fromCond))

        //important also update the templates here         
        if (FunctionInfoFactory.hasTemplate(from)) {
          val toTemplate = mapCalls(replace(substsMap, FunctionInfoFactory.getTemplate(from)))
          //creating new template          
          FunctionInfoFactory.setTemplate(to, toTemplate)
        }
        Some((toResId, toCond))
        
      } else None

      //instrument the bodies of all 'callees' only for tracking depth
      to.body = if (callees.contains(from)) {
        from.body.map(new ExposeDepth(ctx, getCostModel, funMap).apply _)
      } else{        
        val newbody = from.body.map(mapCalls _)        
        newbody
      } 
      
      //copy annotations
      from.annotations.foreach((str) => {        
        to.addAnnotation(str)
      })      
    }
    
    val newDefs = program.mainObject.defs.map {
      case fd: FunDef =>
        funMap(fd)
      case d =>
        d
    }

    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    println("New Prog: \n"+ScalaPrinter.apply(newprog))
    
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

  class ExposeDepth(ctx: LeonContext, cm: CostModel, funMap : Map[FunDef,FunDef]) {

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
    
    def combineDepthIds(depthIds : List[Identifier]) : Expr = {
      depthIds.tail.foldLeft(depthIds.head.toVariable : Expr)((acc, id) => FunctionInvocation(maxFun,Seq(acc, id.toVariable)))      
    }
       
    def tupleifyRecur(e: Expr, args: Seq[Expr], recons: Seq[Expr] => Expr, resIds: List[Identifier], depthIds: List[Identifier]) : Expr = {      
    //note: subs.size should be zero if e is a terminal
      if(args.size == 0)
      {        
        //base case (handle terminals and function invocation separately)
        e match {
          case t : Terminal => Tuple(Seq(recons(Seq()), getCostModel.costOfExpr(e)))
          
          case f@FunctionInvocation(fd,args) => {            
            val newFunInv = FunctionInvocation(funMap(fd),resIds.map(Variable(_)))
            
            //create a variables to store the result of function invocation
            val resvar = FreshIdentifier("e", true).setType(e.getType)
            val depthvar = FreshIdentifier("d", true).setType(Int32Type)            
            
            val costofOp = Plus(getCostModel.costOfExpr(e),Variable(depthvar))
            val depthPart = Plus(costofOp, combineDepthIds(depthIds))
              //timeIds.foldLeft(costofOp: Expr)((g: Expr, t: Identifier) => Plus(Variable(t), g))            
            val baseExpr = Tuple(Seq(Variable(resvar), depthPart))
                                    
            LetTuple(Seq(resvar,depthvar),newFunInv,baseExpr)
          }
          
          case _ => {
            val exprPart = recons(resIds.map(Variable(_)): Seq[Expr])
            val costofOp = getCostModel.costOfExpr(e)
            val depthPart = Plus(costofOp, combineDepthIds(depthIds))
              //timeIds.foldLeft(costofOp: Expr)((g: Expr, t: Identifier) => Plus(Variable(t), g))
            Tuple(Seq(exprPart, depthPart))
          }
        }    	
      }
      else
      {
        //recursion step
        val currentElem = args.head
        val resvar = FreshIdentifier("e", true).setType(currentElem.getType)
        val depthvar = FreshIdentifier("d", true).setType(Int32Type)       
                
        ///recursively call the method on subs.tail
        val recRes = tupleifyRecur(e,args.tail,recons,resIds :+ resvar, depthIds :+ depthvar)
        
        //transform the current element (handle function invocation separately)        
        val newCurrExpr = transform(args.head)
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
        val newexpr = LetTuple(Seq(resvar, depthvar ),newCurrExpr,recRes)
        newexpr
      }      
    }

    //TODO: need to handle Assume 
    def transform(e: Expr): Expr = e match {    
      case Let(i, v, b) =>
        val ir = FreshIdentifier("ir", true).setType(v.getType)
        val it = FreshIdentifier("it", true).setType(Int32Type)
        val r = FreshIdentifier("r", true).setType(e.getType)
        val t = FreshIdentifier("d", true).setType(Int32Type)

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
        val depthcond = FreshIdentifier("t", true).setType(Int32Type)
        
        //transform the then branch        
        val resthen = FreshIdentifier("e", true).setType(then.getType)
        val depththen = FreshIdentifier("t", true).setType(Int32Type)
        val newthen = LetTuple(Seq(resthen,depththen), transform(then), 
            Tuple(Seq(Variable(resthen),Plus(Variable(depthcond),Variable(depththen)))))
                
        //similarly transform the else branch 
        val reselse = FreshIdentifier("e", true).setType(elze.getType)
        val depthelse = FreshIdentifier("t", true).setType(Int32Type)
        val newelse = LetTuple(Seq(reselse,depthelse), transform(elze), 
            Tuple(Seq(Variable(reselse),Plus(Variable(depthcond),Variable(depthelse)))))
                
        //create a final expression
        LetTuple(Seq(rescond,depthcond),transform(cond), IfExpr(Variable(rescond),newthen,newelse))                
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
