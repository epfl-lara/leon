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

object NonlinearityEliminationPhase extends LeonPhase[Program, Program] {
  val name = "Nonlinearity Elimination Phase"
  val description = "Reduces nonlinear functions to recursive functions with axioms"
  val one = IntLiteral(1)
  val zero = IntLiteral(0)

  //a recursive function that represents multiplication of two positive arguments
  val pivMultFun = {
    val xid = FreshIdentifier("x").setType(Int32Type)
    val yid = FreshIdentifier("y").setType(Int32Type)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val mfd = new FunDef(FreshIdentifier("pmult", false), Int32Type, args.map((arg) => VarDecl(arg, arg.getType)))

    //define precondition (not necessary)
    //mfd.precondition = Some(And(GreaterEquals(varx, zero),GreaterEquals(vary, zero)))

    //define a body (a) using mult(x,y) = if(x == 0 || y ==0) 0 else mult(x-1,y) + y 
    val cond = Or(Equals(varx, zero), Equals(vary, zero))
    val xminus1 = Minus(varx, one)
    val yminus1 = Minus(vary, one)
    val elze = Plus(FunctionInvocation(mfd, Seq(xminus1, vary)), vary)
    mfd.body = Some(IfExpr(cond, zero, elze))

    //add postcondition
    val resvar = FreshIdentifier("res").setType(Int32Type).toVariable
    val post0 = GreaterEquals(resvar, zero)

    //define alternate definitions of multiplication as postconditions                  
    //(a) res = !(x==0 || y==0) => mult(x,y-1) + x
    val guard = Not(cond)
    val defn2 = Equals(resvar, Plus(FunctionInvocation(mfd, Seq(varx, yminus1)), varx))
    val post1 = Implies(guard, defn2)

    mfd.postcondition = Some((resvar.id, And(Seq(post0, post1))))

    //set function info properties
    val mfdinfo = FunctionInfoFactory.getOrMakeInfo(mfd)
    mfdinfo.setTheoryOperation
    //create axioms (for now only monotonicity)
    mfdinfo.setMonotonicity
    //mfdinfo.setDistributivity
    mfd
  }

  //a function that represents multiplication, this transitively calls pmult 
  val multFun = {
    val xid = FreshIdentifier("x").setType(Int32Type)
    val yid = FreshIdentifier("y").setType(Int32Type)
    val varx = xid.toVariable
    val vary = yid.toVariable
    val args = Seq(xid, yid)
    val fd = new FunDef(FreshIdentifier("mult", false), Int32Type, args.map((arg) => VarDecl(arg, arg.getType)))

    //the body is defined as mult(x,y) = val px = if(x < 0) -x else x; 
    //val py = if(y<0) -y else y;  val r = pmult(px,py); 
    //if(x < 0 && y < 0 || x >= 0 && y >= 0) r else -r
    val modx = IfExpr(LessThan(varx, zero), UMinus(varx), varx)
    val mody = IfExpr(LessThan(vary, zero), UMinus(vary), vary)
    val px = FreshIdentifier("px", false).setType(Int32Type)
    val py = FreshIdentifier("py", false).setType(Int32Type)
    val call = Let(px, modx, Let(py, mody, FunctionInvocation(pivMultFun, Seq(px, py).map(_.toVariable))))
    val bothPive = And(GreaterEquals(varx, zero), GreaterEquals(vary, zero))
    val bothNive = And(LessThan(varx, zero), LessThan(vary, zero))
    val res = FreshIdentifier("r", false).setType(Int32Type)
    val body = Let(res, call, IfExpr(Or(bothPive, bothNive), res.toVariable, UMinus(res.toVariable)))
    fd.body = Some(body)

    //set function info properties
    val funinfo = FunctionInfoFactory.getOrMakeInfo(fd)
    funinfo.setTheoryOperation
    fd
  }

  //TOOD: note associativity property of multiplication is not taken into account
  def run(ctx: LeonContext)(program: Program): Program = {

    //create a fundef for each function in the program
    val newFundefs = program.mainObject.definedFunctions.map((fd) => {
      val newfd = new FunDef(FreshIdentifier(fd.id.name, false), fd.returnType, fd.args)
      (fd, newfd)
    }).toMap

    //note, handling templates variables is slightly tricky as we need to preserve a*x as it is
    var addMult = false
    def replaceFun(ine: Expr) : Expr = {      
      simplePostTransform(e => e match {
        case fi @ FunctionInvocation(fd1, args) if newFundefs.contains(fd1) =>
          FunctionInvocation(newFundefs(fd1), args)

        case Times(Variable(id), e2) if (TemplateIdFactory.IsTemplateIdentifier(id)) => e
        case Times(e1, Variable(id)) if (TemplateIdFactory.IsTemplateIdentifier(id)) => e

        case Times(e1, e2) if (!e1.isInstanceOf[IntLiteral] && !e2.isInstanceOf[IntLiteral]) => {
          //replace times by a mult function
          addMult = true
          FunctionInvocation(multFun, Seq(e1, e2))
        }
        //note: include mult function if division operation is encountered
        //division is handled during verification condition generation.
        case Division(_, _) => {
          addMult = true
          e
        }
        case _ => e
      })(ine)
    }

    //create a body, pre, post for each newfundef
    newFundefs.foreach((entry) => {
      val (fd, newfd) = entry

      //add a new precondition
      newfd.precondition =
        if (fd.precondition.isDefined)
          Some(replaceFun(fd.precondition.get))
        else None

      //add a new body
      newfd.body = if (fd.hasBody) {
        //replace variables by constants if possible
        val simpBody = simplifyLets(fd.body.get)
        Some(replaceFun(simpBody))
      } else None

      //add a new postcondition                        
      newfd.postcondition = if (fd.postcondition.isDefined) {
        val (resvar, pexpr) = fd.postcondition.get
        Some(resvar, replaceFun(pexpr))
      } else None

      //important: update function info of 'newfd'       
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      if (funinfo.isDefined && funinfo.get.hasTemplate) {        
        FunctionInfoFactory.createFunctionInfo(newfd, replaceFun, funinfo.get)
        //        val toTemplate = simplePostTransform(replaceFun)(FunctionInfoFactory.getTemplate(fd))
        //        FunctionInfoFactory.setTemplate(newfd, toTemplate, FunctionInfoFactory.getTimevar(fd))
      }

      fd.annotations.foreach((str) => newfd.addAnnotation(str))
    })

    val newDefs = program.mainObject.defs.map {
      case fd: FunDef => newFundefs(fd)
      case d => d
    } ++ (if (addMult) Seq(multFun, pivMultFun) else Seq())

    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))
    println("After Nonlinearity Elimination: \n" + ScalaPrinter.apply(newprog))

    //print all the templates
    newprog.definedFunctions.foreach((fd) => {
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      if (funinfo.isDefined && funinfo.get.hasTemplate)
        println("Function: " + fd.id + " template --> " + funinfo.get.getTemplate)
    })
    newprog
  }
}
