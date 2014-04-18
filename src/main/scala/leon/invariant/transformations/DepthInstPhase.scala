package leon
package invariant.transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._

import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._

/**
 * TODO: is it necessary to create new functions even if it does not use depth 
 */
object DepthInstPhase extends LeonPhase[Program,Program] {
  val name = "Expose Depth Phase"
  val description = "Expose depth of a function"  

  val maxFun = {
    val xid = FreshIdentifier("x").setType(Int32Type)
    val yid = FreshIdentifier("y").setType(Int32Type)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val fd = new FunDef(FreshIdentifier("max", true), Seq(), Int32Type, args.map((arg) => ValDef(arg, arg.getType)))
    //add a body    
    fd.body = Some(IfExpr(GreaterEquals(varx, vary), varx, vary))
    fd
  }
  val typedMax = TypedFunDef(maxFun, Seq())
  
  def run(ctx: LeonContext)(program: Program) : Program = {
                
    // Map from old fundefs to new fundefs
	var funMap = Map[FunDef, FunDef]()
  
	//find functions that use depth in the postcondition or are transitively called from such functions
	var rootFuncs = Set[FunDef]()
	program.definedFunctions.foreach((fd) => { 
	  if(fd.hasPostcondition 
	      && ExpressionTransformer.isSubExpr(DepthVariable(), fd.postcondition.get._2)) {
	    rootFuncs += fd
	  } else {
        val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
        if (funinfo.isDefined && funinfo.get.hasTemplate &&
          ExpressionTransformer.isSubExpr(DepthVariable(), funinfo.get.getTemplate)) {
          rootFuncs += fd
        }
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
        case FunctionInvocation(TypedFunDef(fd, tps), args) =>
          if (callees.contains(fd)) {
            TupleSelect(FunctionInvocation(TypedFunDef(funMap(fd),tps), args), 1)
          } else {
            val fi = FunctionInvocation(TypedFunDef(funMap(fd),tps), args)           
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

        //important also update the function info here
        val frominfo = FunctionInfoFactory.getFunctionInfo(from)
        if (frominfo.isDefined) {
          val transfunc = (e: Expr) => mapCalls(replace(substsMap, e))
          FunctionInfoFactory.createFunctionInfo(to, transfunc, frominfo.get)
        }
          
        //set the depth information
        if (substsMap.contains(DepthVariable())) {
          val toinfo = FunctionInfoFactory.getOrMakeInfo(to)
          toinfo.setDepthexpr(substsMap(DepthVariable()))
        }
        //          //creating new template
        //          val timeexpr = FunctionInfoFactory.getTimevar(from)
        //          val newTimeExpr = if(timeexpr.isDefined) {
        //            Some(replace(substsMap, timeexpr.get))
        //          } else None
        //          FunctionInfoFactory.setTemplate(to, toTemplate, newTimeExpr)
        //        }
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
    
    val newprog = Util.copyProgram(program, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => funMap(fd)
      case d => d
    } ++ {
      if(!rootFuncs.isEmpty) Seq(maxFun) else Seq() 
    })
    //println("After Depth Instrumentation: \n"+ScalaPrinter.apply(newprog))
    
    //print all the templates
    //newprog.definedFunctions.foreach((fd) => println("Defined fun: "+fd.id)) 
      /*if(FunctionInfoFactory.hasTemplate(fd))
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
    def tupleify(e: Expr, args: Seq[Expr], recons: Seq[Expr] => Expr, letIdToDepth: Map[Identifier,Identifier]): Expr = {
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
        tupleifyRecur(e, args, recons, List[Identifier](),List[Identifier](), letIdToDepth)
    }
    
    def combineDepthIds(costofOp: Expr, depthIds : List[Identifier]) : Expr = {
      if(depthIds.size == 0) costofOp
      else if(depthIds.size == 1) Plus(costofOp, depthIds(0).toVariable)
      else {
        //optimization: remove duplicates from 'depthIds' as 'max' is an idempotent operation
        val head +: tail = depthIds.distinct
        val summand = tail.foldLeft(head.toVariable : Expr)((acc, id) => {
          FunctionInvocation(typedMax,Seq(acc, id.toVariable))
        })
        Plus(costofOp, summand)
      }           
    }
       
    def tupleifyRecur(e: Expr, args: Seq[Expr], recons: Seq[Expr] => Expr, 
        resIds: List[Identifier], 
        depthIds: List[Identifier],
        letIdToDepth : Map[Identifier, Identifier]) : Expr = {      
      
      if(args.size == 0)
      {               
        //This will be entered when all the arguments have been processed, the current root of the AST
        e match {
          case Variable(id) if(letIdToDepth.contains(id)) => {
            val depth = Plus(getCostModel.costOfExpr(e), letIdToDepth(id).toVariable)
            Tuple(Seq(recons(Seq()), depth))
          }
          case t : Terminal => {            
            Tuple(Seq(recons(Seq()), getCostModel.costOfExpr(t)))
          }
          
          case f@FunctionInvocation(TypedFunDef(fd,tps),args) => {            
            val newFunInv = FunctionInvocation(TypedFunDef(funMap(fd),tps),resIds.map(Variable(_)))
            
            //create a variables to store the result of function invocation
            val resvar = FreshIdentifier("e", true).setType(e.getType)
            val depthvar = FreshIdentifier("d", true).setType(Int32Type)            
            
            val costofOp = Plus(getCostModel.costOfExpr(e),Variable(depthvar))
            val depthPart = combineDepthIds(costofOp, depthIds)                       
            val baseExpr = Tuple(Seq(Variable(resvar), depthPart))
                                    
            LetTuple(Seq(resvar,depthvar),newFunInv,baseExpr)
          }
          
          case _ => {
            val exprPart = recons(resIds.map(Variable(_)): Seq[Expr])
            val costofOp = getCostModel.costOfExpr(e)
            val depthPart = combineDepthIds(costofOp, depthIds)             
            Tuple(Seq(exprPart, depthPart))
          }
        }    	
      }
      else
      {
        //the processing of args
        val currentElem = args.head
        val resvar = FreshIdentifier("r", true).setType(currentElem.getType)
        val depthvar = FreshIdentifier("d", true).setType(Int32Type)       
                
        ///recursively call the method on args.tail
        val recRes = tupleifyRecur(e, args.tail, recons, resIds :+ resvar, depthIds :+ depthvar, letIdToDepth)
        
        //transform the current element (handle function invocation separately)        
        val newCurrExpr = transform(args.head, letIdToDepth)        
        
        //create the new expression for the current recursion step
        val newexpr = LetTuple(Seq(resvar, depthvar),newCurrExpr,recRes)
        newexpr
      }      
    }

    //TODO: need to handle Assume 
    def transform(e: Expr, letIdToDepth : Map[Identifier, Identifier]): Expr = e match {    
      case Let(i, v, b) =>
        val vres = FreshIdentifier("vr", true).setType(v.getType)
        val vdepth = FreshIdentifier("vd", true).setType(Int32Type)
        val bres = FreshIdentifier("br", true).setType(e.getType)
        val bdepth = FreshIdentifier("bd", true).setType(Int32Type)
        
        val newvalue = transform(v, letIdToDepth)
        val newbody = transform(replace(Map(Variable(i) -> Variable(vres)), b),
            letIdToDepth + (vres -> vdepth))

        LetTuple(Seq(vres, vdepth), newvalue,
          LetTuple(Seq(bres,bdepth),  newbody,
            Tuple(Seq(Variable(bres), Plus(Variable(bdepth), cm.costOfExpr(e))))
            )
          )        
      
      case LetTuple(ids, v, b) =>
        val vres = FreshIdentifier("vres", true).setType(v.getType)
        val vdepth = FreshIdentifier("vdepth", true).setType(Int32Type)
        val bres = FreshIdentifier("bres", true).setType(e.getType)
        val bdepth = FreshIdentifier("bdepth", true).setType(Int32Type)
        
        val newvalue = transform(v, letIdToDepth)
        val newbody = transform(b, letIdToDepth ++ ids.map((id) => (id -> vdepth)))
        
        //TODO: reusing the same 'ids' is it safe ??
        LetTuple(Seq(vres, vdepth), newvalue,
         LetTuple(ids, vres.toVariable,
          LetTuple(Seq(bres,bdepth), newbody,
            Tuple(Seq(Variable(bres), Plus(Variable(bdepth), cm.costOfExpr(e))))
            )            
          )
        )

      case IfExpr(cond, then, elze) =>{               
        //depth of if(cond) e1 else e2 is if(cond) max(d_cond, d_e1) else max(dcond, d_e2)  
        val rescond = FreshIdentifier("rcond", true).setType(cond.getType)
        val depthcond = FreshIdentifier("dcond", true).setType(Int32Type)
        val newcond = transform(cond, letIdToDepth)
        
        //transform the then branch        
        val resthen = FreshIdentifier("rthen", true).setType(then.getType)
        val depththen = FreshIdentifier("dthen", true).setType(Int32Type)
        val depthtres = FunctionInvocation(typedMax, Seq(Variable(depthcond),Variable(depththen)))
        val newthen = LetTuple(Seq(resthen,depththen), transform(then, letIdToDepth), 
            Tuple(Seq(Variable(resthen), depthtres)))
                
        //similarly transform the else branch 
        val reselse = FreshIdentifier("relse", true).setType(elze.getType)
        val depthelse = FreshIdentifier("delse", true).setType(Int32Type)
        val deptheres = FunctionInvocation(typedMax, Seq(Variable(depthcond),Variable(depthelse)))

        val newelse = LetTuple(Seq(reselse,depthelse), transform(elze, letIdToDepth), 
            Tuple(Seq(Variable(reselse),deptheres)))
                
        //create a final expression
        LetTuple(Seq(rescond,depthcond), newcond, IfExpr(Variable(rescond),newthen,newelse))                
      }
        
      // For all other operations, we go through a common tupleifier.
      case n @ NAryOperator(args, recons) =>
        tupleify(e, args, recons, letIdToDepth)

      case b @ BinaryOperator(s1, s2, recons) =>
        tupleify(e, Seq(s1, s2), { case Seq(s1, s2) => recons(s1, s2) }, letIdToDepth)

      case u @ UnaryOperator(s, recons) =>
        tupleify(e, Seq(s), { case Seq(s) => recons(s) }, letIdToDepth)

      case t: Terminal =>
        tupleify(e, Seq(), { case Seq() => t }, letIdToDepth)
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
      //Initially the mapping from letIdToDepth is empty (optionally we could add parameters with depth 0)
      val res    = transform(input, Map())      
      val simple = simplifyMax(simplifyLets(res))

      // For debugging purposes            
      /*println("-"*80)
      println("AFTER:")      
      println(simple)*/
      simple
    }
    
    def simplifyMax(ine: Expr) : Expr = {
      simplePostTransform((e: Expr) => e match {
        case FunctionInvocation(fd, args) if(fd == maxFun)  => {
          val Seq(arg1, arg2) = args
          (arg1, arg2) match {
            case (a1@IntLiteral(v1), a2@IntLiteral(v2)) => if(v1 >= v2) a1 else a2
            case _ => {
               //here inline the maxFun (optimization)
              IfExpr(GreaterEquals(arg1,arg2), arg1, arg2)
            }
          }                             
        }
        case _ => simplifyArithmetic(e)        
      })(ine)
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
