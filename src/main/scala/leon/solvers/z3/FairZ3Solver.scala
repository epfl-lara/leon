/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package z3

import _root_.z3.scala._

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._

import unrolling._
import theories._
import utils._

class FairZ3Solver(val sctx: SolverContext, val program: Program)
  extends AbstractZ3Solver
     with AbstractUnrollingSolver[Z3AST] {

  enclosing =>

  protected val errors     = new IncrementalBijection[Unit, Boolean]()
  protected def hasError   = errors.getB(()) contains true
  protected def addError() = errors += () -> true

  override val name = "Z3-f"
  override val description = "Fair Z3 Solver"

  override def reset(): Unit = super[AbstractZ3Solver].reset()

  def declareVariable(id: Identifier): Z3AST = variables.cachedB(Variable(id)) {
    templateEncoder.encodeId(id)
  }

  def solverCheck[R](clauses: Seq[Z3AST])(block: Option[Boolean] => R): R = {
    solver.push()
    for (cls <- clauses) solver.assertCnstr(cls)
    val res = solver.check
    val r = block(res)
    solver.pop()
    r
  }

  override def solverCheckAssumptions[R](assumptions: Seq[Z3AST])(block: Option[Boolean] => R): R = {
    solver.push() // FIXME: remove when z3 bug is fixed
    val res = solver.checkAssumptions(assumptions : _*)
    solver.pop()  // FIXME: remove when z3 bug is fixed
    block(res)
  }

  def solverGetModel: ModelWrapper = new ModelWrapper {
    val model: Z3Model = solver.getModel

    /*
    val functionsModel: Map[Z3FuncDecl, (Seq[(Seq[Z3AST], Z3AST)], Z3AST)] = model.getModelFuncInterpretations.map(i => (i._1, (i._2, i._3))).toMap
    val functionsAsMap: Map[Identifier, Expr] = functionsModel.flatMap(p => {
      if (functions containsB p._1) {
        val tfd = functions.toA(p._1)
        if (!tfd.hasImplementation) {
          val (cses, default) = p._2
          val ite = cses.foldLeft(fromZ3Formula(model, default, tfd.returnType))((expr, q) => IfExpr(
            andJoin(q._1.zip(tfd.params).map(a12 => Equals(fromZ3Formula(model, a12._1, a12._2.getType), Variable(a12._2.id)))),
            fromZ3Formula(model, q._2, tfd.returnType),
            expr))
          Seq((tfd.id, ite))
        } else Seq()
      } else Seq()
    })

    val constantFunctionsAsMap: Map[Identifier, Expr] = model.getModelConstantInterpretations.flatMap(p => {
      if(functions containsB p._1) {
        val tfd = functions.toA(p._1)
        if(!tfd.hasImplementation) {
          Seq((tfd.id, fromZ3Formula(model, p._2, tfd.returnType)))
        } else Seq()
      } else Seq()
    }).toMap

    val leonModel = extractModel(model, freeVars.toSet)
    val fullModel = leonModel ++ (functionsAsMap ++ constantFunctionsAsMap)
    */

    def modelEval(elem: Z3AST, tpe: TypeTree): Option[Expr] = {
      val timer = context.timers.solvers.z3.eval.start()
      val res = tpe match {
        case BooleanType => model.evalAs[Boolean](elem).map(BooleanLiteral)
        case Int32Type => model.evalAs[Int](elem).map(IntLiteral).orElse {
          model.eval(elem).flatMap(t => softFromZ3Formula(model, t, Int32Type))
        }
        case IntegerType => model.evalAs[Int](elem).map(InfiniteIntegerLiteral(_))
        case other => model.eval(elem) match {
          case None => None
          case Some(t) => softFromZ3Formula(model, t, other)
        }
      }
      timer.stop()
      res
    }

    override def toString = model.toString
  }

  val printable = (z3: Z3AST) => new Printable {
    def asString(implicit ctx: LeonContext) = z3.toString
  }

  val theoryEncoder = new StringEncoder(context, program) >> new BagEncoder(context, program)

  val templateEncoder = new TemplateEncoder[Z3AST] {
    def encodeId(id: Identifier): Z3AST = {
      idToFreshZ3Id(id)
    }

    def encodeExpr(bindings: Map[Identifier, Z3AST])(e: Expr): Z3AST = {
      toZ3Formula(e, bindings)
    }

    def substitute(substMap: Map[Z3AST, Z3AST]): Z3AST => Z3AST = {
      val (from, to) = substMap.unzip
      val (fromArray, toArray) = (from.toArray, to.toArray)

      (c: Z3AST) => z3.substitute(c, fromArray, toArray)
    }

    def mkNot(e: Z3AST) = z3.mkNot(e)
    def mkOr(es: Z3AST*) = z3.mkOr(es : _*)
    def mkAnd(es: Z3AST*) = z3.mkAnd(es : _*)
    def mkEquals(l: Z3AST, r: Z3AST) = z3.mkEq(l, r)
    def mkImplies(l: Z3AST, r: Z3AST) = z3.mkImplies(l, r)

    def extractNot(l: Z3AST): Option[Z3AST] = z3.getASTKind(l) match {
      case Z3AppAST(decl, args) => z3.getDeclKind(decl) match {
        case Z3DeclKind.OpNot => Some(args.head)
        case Z3DeclKind.OpUninterpreted => None
      }
      case ast => None
    }
  }

  private val incrementals: List[IncrementalState] = List(
    errors, functions, lambdas, sorts, variables,
    constructors, selectors, testers
  )

  override def push(): Unit = {
    super.push()
    solver.push()
    incrementals.foreach(_.push())
  }

  override def pop(): Unit = {
    super.pop()
    solver.pop(1)
    incrementals.foreach(_.pop())
  }

  override def check: Option[Boolean] = {
    if (hasError) {
      None
    } else {
      super.check
    }
  }

  override def checkAssumptions(assumptions: Set[Expr]): Option[Boolean] = {
    if (hasError) {
      None
    } else {
      super.checkAssumptions(assumptions)
    }
  }

  override def assertCnstr(expression: Expr): Unit = {
    try {
      super.assertCnstr(expression)
    } catch {
      case u: Unsupported =>
        addError()
    }
  }

  def solverAssert(cnstr: Z3AST): Unit = {
    val timer = context.timers.solvers.z3.assert.start()
    solver.assertCnstr(cnstr)
    timer.stop()
  }

  def solverUnsatCore = Some(solver.getUnsatCore)

  override def foundAnswer(res: Option[Boolean], model: Model = Model.empty, core: Set[Expr] = Set.empty) = {
    super.foundAnswer(res, model, core)

    if (!interrupted && res.isEmpty && model.isEmpty) {
      reporter.ifDebug { debug => 
        if (solver.getReasonUnknown != "canceled") {
          debug("Z3 returned unknown: " + solver.getReasonUnknown)
        }
      }
    }
  }

  override def interrupt(): Unit = {
    super[AbstractZ3Solver].interrupt()
    super[AbstractUnrollingSolver].interrupt()
  }
}
