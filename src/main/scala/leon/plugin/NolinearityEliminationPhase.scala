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

object NonlinearityEliminationPhase extends LeonPhase[Program,Program] {
  val name = "Nonlinearity Elimination Phase"
  val description = "Reduces nonlinear functions to recursive functions with axioms"
  val one = IntLiteral(1)   
  val zero = IntLiteral(0)
    
  //a user defined function that represents multiplication (only for positive arguments)
  //TODO: define a full multiplication using piveMult
  val piveMultFun  = {    
      //create new multFun
      val xid = FreshIdentifier("x").setType(Int32Type)
      val yid = FreshIdentifier("y").setType(Int32Type)
      val varx = xid.toVariable
      val vary = yid.toVariable
      val args = Seq(xid, yid)
      val mfd = new FunDef(FreshIdentifier("mult", false), Int32Type, args.map((arg) => VarDecl(arg, arg.getType)))
      
      //define precondition
      mfd.precondition = Some(And(GreaterEquals(varx, zero),GreaterEquals(vary, zero)))
      
      //define a body (a) using mult(x,y) = if(x == 0 || y ==0) 0 else mult(x-1,y) + y 
      val cond = Or(Equals(varx,zero),Equals(vary,zero))      
      val xminus1 = Minus(varx, one)
      val yminus1 = Minus(vary, one)      
      val elze = Plus(FunctionInvocation(mfd, Seq(xminus1,vary)), vary)
      mfd.body = Some(IfExpr(cond, zero, elze))
      
      //add postcondition
      val resvar = FreshIdentifier("res").setType(Int32Type).toVariable
      val post0 = GreaterEquals(resvar,zero)
      
      //define alternate definitions of multiplication as postconditions                  
      //(a) res = !(x==0 || y==0) => mult(x,y-1) + x
      val guard = Not(cond)                  
      val defn2 = Equals(resvar,Plus(FunctionInvocation(mfd, Seq(varx,yminus1)), varx))
      val post1 = Implies(guard, defn2)
      
      mfd.postcondition = Some((resvar.id, And(Seq(post0, post1))))                       
      //create axioms (for now only monotonicity)      
      FunctionInfoFactory.setMonotonicity(mfd)
      
      //make this a theory operation
      FunctionInfoFactory.setTheoryOperation(mfd)
      mfd      
    }

  //TOOD: note associativity property of multiplication is not taken into account
  def run(ctx: LeonContext)(program: Program) : Program = {
           
    //create a fundef for each function in the program
    val newFundefs = program.mainObject.definedFunctions.map((fd) => {
      val newfd = new FunDef(FreshIdentifier(fd.id.name, false), fd.returnType, fd.args)
      (fd, newfd)
    }).toMap 

    var addMult = false
    val replaceFun = (e: Expr) => e match {      
      case fi @ FunctionInvocation(fd1, args) if newFundefs.contains(fd1) =>
        FunctionInvocation(newFundefs(fd1), args)
        
      //handle templates
      case Times(Variable(id), e2) if(TemplateIdFactory.IsTemplateIdentifier(id)) => e
      case Times(e1, Variable(id)) if(TemplateIdFactory.IsTemplateIdentifier(id)) => e
      
      case Times(e1, e2) if (!e1.isInstanceOf[IntLiteral] && !e2.isInstanceOf[IntLiteral]) => {
        //replace times by a mult function
        addMult = true        
        FunctionInvocation(piveMultFun, Seq(e1, e2))
      }      
      case _ => e
    }

    //create a body, pre, post for each newfundef
    newFundefs.foreach((entry) => {
      val (fd, newfd) = entry

      //add a new precondition
      newfd.precondition =
        if (fd.precondition.isDefined)
          Some(simplePostTransform(replaceFun)(fd.precondition.get))
        else None

      //add a new body
      newfd.body = if (fd.hasBody){
        //replace variables by constants if possible
        val simpBody = simplifyLets(fd.body.get)
        Some(simplePostTransform(replaceFun)(simpBody))        
      }        
      else None

      //add a new postcondition                        
      newfd.postcondition = if (fd.postcondition.isDefined) {
        val (resvar, pexpr) = fd.postcondition.get
        Some(resvar, simplePostTransform(replaceFun)(pexpr))
      } else None
      
      //important: also set the templates for newfd 
      //note handling templates is slightly tricky as we need to preserve a*x as it is
      if (FunctionInfoFactory.hasTemplate(fd)) {
          val toTemplate =  simplePostTransform(replaceFun)(FunctionInfoFactory.getTemplate(fd))                 
          FunctionInfoFactory.setTemplate(newfd, toTemplate)
        }
    })

    val newDefs = program.mainObject.defs.map {
      case fd: FunDef => newFundefs(fd)
      case d => d
    } ++  (if(addMult) Seq(piveMultFun) else Seq())

    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    //println("Program: "+newprog)
    println("New Prog: \n"+ScalaPrinter.apply(newprog))
    
    //print all the templates
    newprog.definedFunctions.foreach((fd) => 
      if(FunctionInfoFactory.hasTemplate(fd))
        println("Function: "+fd.id+" template --> "+FunctionInfoFactory.getTemplate(fd))
        )
    newprog
  }
}
