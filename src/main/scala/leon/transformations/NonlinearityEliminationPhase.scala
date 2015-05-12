package leon
package transformations

import invariant.factories._
import invariant.util.Util._
import invariant.structure.FunctionUtils._

import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._

object MultFuncs {
  def getMultFuncs(domain: TypeTree): (FunDef, FunDef) = {
    //a recursive function that represents multiplication of two positive arguments
    val pivMultFun = {
      val xid = FreshIdentifier("x", domain)
      val yid = FreshIdentifier("y", domain)
      val varx = xid.toVariable
      val vary = yid.toVariable
      val args = Seq(xid, yid)
      val funcType = FunctionType(Seq(domain, domain), domain)
      val mfd = new FunDef(FreshIdentifier("pmult", funcType, false), Seq(), domain,
        args.map((arg) => ValDef(arg, Some(arg.getType))))
      val tmfd = TypedFunDef(mfd, Seq())

      //define a body (a) using mult(x,y) = if(x == 0 || y ==0) 0 else mult(x-1,y) + y
      val cond = Or(Equals(varx, zero), Equals(vary, zero))
      val xminus1 = Minus(varx, one)
      val yminus1 = Minus(vary, one)
      val elze = Plus(FunctionInvocation(tmfd, Seq(xminus1, vary)), vary)
      mfd.body = Some(IfExpr(cond, zero, elze))

      //add postcondition
      val resvar = FreshIdentifier("res", domain).toVariable
      val post0 = GreaterEquals(resvar, zero)

      //define alternate definitions of multiplication as postconditions
      //(a) res = !(x==0 || y==0) => mult(x,y-1) + x
      val guard = Not(cond)
      val defn2 = Equals(resvar, Plus(FunctionInvocation(tmfd, Seq(varx, yminus1)), varx))
      val post1 = Implies(guard, defn2)

      // mfd.postcondition = Some((resvar.id, And(Seq(post0, post1))))
      mfd.fullBody = Ensuring(mfd.body.get, Lambda(Seq(ValDef(resvar.id, Some(resvar.getType))), And(Seq(post0, post1))))
      //set function properties (for now, only monotonicity)
      mfd.addFlags(Set(Annotation("theoryop", Seq()), Annotation("monotonic", Seq()))) //"distributive" ?
      mfd
    }

    //a function that represents multiplication, this transitively calls pmult
    val multFun = {
      val xid = FreshIdentifier("x", domain)
      val yid = FreshIdentifier("y", domain)
      val args = Seq(xid, yid)
      val funcType = FunctionType(Seq(domain, domain), domain)
      val fd = new FunDef(FreshIdentifier("mult", funcType, false), Seq(), domain, args.map((arg) => ValDef(arg, Some(arg.getType))))
      val tpivMultFun = TypedFunDef(pivMultFun, Seq())

      //the body is defined as mult(x,y) = val px = if(x < 0) -x else x;
      //val py = if(y<0) -y else y;  val r = pmult(px,py);
      //if(x < 0 && y < 0 || x >= 0 && y >= 0) r else -r
      val varx = xid.toVariable
      val vary = yid.toVariable
      val modx = IfExpr(LessThan(varx, zero), UMinus(varx), varx)
      val mody = IfExpr(LessThan(vary, zero), UMinus(vary), vary)
      val px = FreshIdentifier("px", domain, false)
      val py = FreshIdentifier("py", domain, false)
      val call = Let(px, modx, Let(py, mody, FunctionInvocation(tpivMultFun, Seq(px, py).map(_.toVariable))))
      val bothPive = And(GreaterEquals(varx, zero), GreaterEquals(vary, zero))
      val bothNive = And(LessThan(varx, zero), LessThan(vary, zero))
      val res = FreshIdentifier("r", domain, false)
      val body = Let(res, call, IfExpr(Or(bothPive, bothNive), res.toVariable, UMinus(res.toVariable)))
      fd.body = Some(body)
      //set function properties
      fd.addFlags(Set(Annotation("theoryop", Seq()), Annotation("monotonic", Seq())))
      fd
    }

    (pivMultFun, multFun)
  }
}

class NonlinearityEliminator(skipAxioms: Boolean, domain: TypeTree) {
  import MultFuncs._
  require(isNumericType(domain))

  val debugNLElim = false

  val one = InfiniteIntegerLiteral(1)
  val zero = InfiniteIntegerLiteral(0)

  val (pivMultFun, multFun) = getMultFuncs(domain)

  //TOOD: note associativity property of multiplication is not taken into account
  def apply(program: Program): Program = {

    //create a fundef for each function in the program
    val newFundefs = program.definedFunctions.map((fd) => {
      val newFunType = FunctionType(fd.tparams.map((currParam) => currParam.tp), fd.returnType)
      val newfd = new FunDef(FreshIdentifier(fd.id.name, newFunType, false), fd.tparams, fd.returnType, fd.params)
      (fd, newfd)
    }).toMap

    //note, handling templates variables is slightly tricky as we need to preserve a*x as it is
    val tmult = TypedFunDef(multFun, Seq())
    var addMult = false
    def replaceFun(ine: Expr, allowedVars: Set[Identifier] = Set()): Expr = {
      simplePostTransform(e => e match {
        case fi @ FunctionInvocation(tfd1, args) if newFundefs.contains(tfd1.fd) =>
          FunctionInvocation(TypedFunDef(newFundefs(tfd1.fd), tfd1.tps), args)

        case Times(Variable(id), e2) if (allowedVars.contains(id)) => e
        case Times(e1, Variable(id)) if (allowedVars.contains(id)) => e

        case Times(e1, e2) if (!e1.isInstanceOf[Literal[_]] && !e2.isInstanceOf[Literal[_]]) => {
          //replace times by a mult function
          addMult = true
          FunctionInvocation(tmult, Seq(e1, e2))
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
        //we need to handle template and postWoTemplate specially
        val Lambda(resultBinders, _) = fd.postcondition.get
        val tmplExpr = fd.templateExpr
        val newpost = if (fd.hasTemplate) {
          val FunctionInvocation(tmpfd, Seq(Lambda(tmpvars, tmpbody))) = tmplExpr.get
          val newtmp = FunctionInvocation(tmpfd, Seq(Lambda(tmpvars,
            replaceFun(tmpbody, tmpvars.map(_.id).toSet))))
          fd.postWoTemplate match {
            case None =>
              newtmp
            case Some(postExpr) =>
              And(replaceFun(postExpr), newtmp)
          }
        } else
          replaceFun(fd.getPostWoTemplate)

        Some(Lambda(resultBinders, newpost))
      } else None

      fd.flags.foreach(newfd.addFlag(_))
    })

    val newprog = copyProgram(program, (defs: Seq[Definition]) => {
      defs.map {
        case fd: FunDef => newFundefs(fd)
        case d => d
      } ++ (if (addMult) Seq(multFun, pivMultFun) else Seq())
    })

    if (debugNLElim)
      println("After Nonlinearity Elimination: \n" + ScalaPrinter.apply(newprog))

    newprog
  }
}
