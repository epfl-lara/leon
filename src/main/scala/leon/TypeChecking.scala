/* Copyright 2009-2013 EPFL, Lausanne */

package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object TypeChecking extends UnitPhase[Program] {

  val name = "Type Checking"
  val description = "Type check the AST"

  def apply(ctx: LeonContext, pgm: Program): Unit = {
    val allFuns = pgm.definedFunctions

    allFuns.foreach(fd  => {
      fd.precondition.foreach(typeCheck)
      fd.postcondition.foreach(typeCheck)
      fd.body.foreach(typeCheck)
    })
  }

  private def typeCheck(expr: Expr): Unit = { //expr match {
    //quick hack
    //searchAndReplaceDFS(e => {
    //  if(e.getType == Untyped) {
    //    println("Expression is untyped: " + e)
    //  }
    //  None
    //})(expr)

    //case l@Let(i, v, b) => {
    //  if(l.getType == Untyp
    //  val vr = transform(v)
    //  v.getType match {
    //    case ArrayType(_) => {
    //      val freshIdentifier = FreshIdentifier("t").setType(vr.getType)
    //      id2id += (i -> freshIdentifier)
    //      val br = transform(b)
    //      LetVar(freshIdentifier, vr, br)
    //    }
    //    case _ => {
    //      val br = transform(b)
    //      Let(i, vr, br)
    //    }
    //  }
    //}
    //case LetVar(id, e, b) => {
    //  val er = transform(e)
    //  val br = transform(b)
    //  LetVar(id, er, br)
    //}
    //case wh@While(c, e) => {
    //  val newWh = While(transform(c), transform(e))
    //  newWh.invariant = wh.invariant.map(i => transform(i))
    //  newWh.setPosInfo(wh)
    //}

    //case ite@IfExpr(c, t, e) => {
    //  val rc = transform(c)
    //  val rt = transform(t)
    //  val re = transform(e)
    //  IfExpr(rc, rt, re).setType(rt.getType)
    //}

    //case m @ MatchExpr(scrut, cses) => {
    //  val scrutRec = transform(scrut)
    //  val csesRec = cses.map{
    //    case SimpleCase(pat, rhs) => SimpleCase(pat, transform(rhs))
    //    case GuardedCase(pat, guard, rhs) => GuardedCase(pat, transform(guard), transform(rhs))
    //  }
    //  val tpe = csesRec.head.rhs.getType
    //  MatchExpr(scrutRec, csesRec).setType(tpe).setPosInfo(m)
    //}
    //case LetDef(fd, b) => {
    //  val newFd = if(fd.hasImplementation) {
    //    val body = fd.body.get
    //    val args = fd.args
    //    val newFd = 
    //      if(args.exists(vd => containsArrayType(vd.tpe)) || containsArrayType(fd.returnType)) {
    //        val newArgs = args.map(vd => {
    //          val freshId = FreshIdentifier(vd.id.name).setType(transform(vd.tpe))
    //          id2id += (vd.id -> freshId)
    //          val newTpe = transform(vd.tpe)
    //          VarDecl(freshId, newTpe)
    //        })
    //        val freshFunName = FreshIdentifier(fd.id.name)
    //        val freshFunDef = new FunDef(freshFunName, transform(fd.returnType), newArgs)
    //        fd2fd += (fd -> freshFunDef)
    //        freshFunDef.precondition = fd.precondition.map(transform)
    //        freshFunDef.postcondition = fd.postcondition.map(transform)
    //        freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
    //        freshFunDef
    //      } else fd
    //    val newBody = transform(body)
    //    newFd.body = Some(newBody)
    //    newFd
    //  } else fd
    //  val rb = transform(b)
    //  LetDef(newFd, rb)
    //}
    //case FunctionInvocation(fd, args) => {
    //  val rargs = args.map(transform)
    //  val rfd = fd2fd.get(fd).getOrElse(fd)
    //  FunctionInvocation(rfd, rargs)
    //}

    //case n @ NAryOperator(args, recons) => recons(args.map(transform)).setType(n.getType)
    //case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2)).setType(b.getType)
    //case u @ UnaryOperator(a, recons) => recons(transform(a)).setType(u.getType)

    //case v @ Variable(id) => if(id2id.isDefinedAt(id)) Variable(id2id(id)) else v
    //case (t: Terminal) => t
    //case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)
  }

}
