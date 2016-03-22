/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }
import leon.invariant._
import invariant.engine._
import invariant.factories._
import invariant.structure._
import FunctionUtils._
import scala.annotation.tailrec
import PredicateUtil._
import ProgramUtil._
import TypeUtil._
import Util._
import solvers._
import purescala.DefOps._

object ProgramUtil {

  def createLeonContext(ctx: LeonContext, opts: String*): LeonContext = {
    Main.processOptions(opts.toList).copy(reporter = ctx.reporter,
      interruptManager = ctx.interruptManager, files = ctx.files, timers = ctx.timers)
  }

  /**
   * Here, we exclude empty units that do not have any modules and empty
   * modules that do not have any definitions
   */
  def copyProgram(prog: Program, mapdefs: (Seq[Definition] => Seq[Definition])): Program = {
    prog.copy(units = prog.units.collect {
      case unit if unit.defs.nonEmpty => unit.copy(defs = unit.defs.collect {
        case module: ModuleDef if module.defs.nonEmpty =>
          module.copy(defs = mapdefs(module.defs))
        case other => other
      })
    })
  }

  def appendDefsToModules(p: Program, defs: Map[ModuleDef, Traversable[Definition]]): Program = {
    val res = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m: ModuleDef if defs.contains(m) =>
            m.copy(defs = m.defs ++ defs(m))
          case other => other
        })
    })
    res
  }

  def addDefs(p: Program, defs: Traversable[Definition], after: Definition): Program = {
    var found = false
    val res = p.copy(units = for (u <- p.units) yield {
      u.copy(
        defs = u.defs.map {
          case m: ModuleDef =>
            val newdefs = for (df <- m.defs) yield {
              df match {
                case `after` =>
                  found = true
                  after +: defs.toSeq
                case d =>
                  Seq(d)
              }
            }
            m.copy(defs = newdefs.flatten)
          case other => other
        })
    })
    if (!found) {
      println("addDefs could not find anchor definition!")
    }
    res
  }

  def createTemplateFun(plainTemp: Expr): FunctionInvocation = {
    val tmpl = Lambda(getTemplateIds(plainTemp).toSeq.map(id => ValDef(id)), plainTemp)
    val tmplFd = new FunDef(FreshIdentifier("tmpl", FunctionType(Seq(tmpl.getType), BooleanType), false), Seq(),
      Seq(ValDef(FreshIdentifier("arg", tmpl.getType))), BooleanType)
    tmplFd.body = Some(BooleanLiteral(true))
    FunctionInvocation(TypedFunDef(tmplFd, Seq()), Seq(tmpl))
  }

  /**
   * This is the default template generator.
   * Note: we are not creating template for libraries.
   */
  def getOrCreateTemplateForFun(fd: FunDef): Expr = {
    val plainTemp = if (fd.hasTemplate) fd.getTemplate
    else if (fd.annotations.contains("library")) BooleanLiteral(true)
    else {
      //just consider all the arguments, return values that are integers
      val baseTerms = fd.params.filter((vardecl) => isNumericType(vardecl.getType)).map(_.toVariable) ++
        (if (isNumericType(fd.returnType)) Seq(getFunctionReturnVariable(fd))
        else Seq())
      val lhs = baseTerms.foldLeft(TemplateIdFactory.freshTemplateVar(): Expr)((acc, t) => {
        Plus(Times(TemplateIdFactory.freshTemplateVar(), t), acc)
      })
      val tempExpr = LessEquals(lhs, InfiniteIntegerLiteral(0))
      tempExpr
    }
    plainTemp
  }

  def mapFunctionsInExpr(funmap: Map[FunDef, FunDef])(ine: Expr): Expr = {
    simplePostTransform {
      case FunctionInvocation(tfd, args) if funmap.contains(tfd.fd) =>
        FunctionInvocation(TypedFunDef(funmap(tfd.fd), tfd.tps), args)
      case e => e
    }(ine)
  }

  /**
   * For functions for which `funToTmpl` is not defined, their templates will be removed.
   * Will only consider user-level functions.
   */
  def assignTemplateAndCojoinPost(funToTmpl: Map[FunDef, Expr], prog: Program,
                                  funToPost: Map[FunDef, Expr] = Map(), uniqueIdDisplay: Boolean = false): Program = {

    val keys = funToTmpl.keySet ++ funToPost.keySet
    val userLevelFuns = userLevelFunctions(prog).toSet
    if(!keys.diff(userLevelFuns).isEmpty)
      throw new IllegalStateException("AssignTemplate function called on library functions: "+ keys.diff(userLevelFuns))

    val funMap = userLevelFuns.foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) => {
        val freshId = FreshIdentifier(fd.id.name, fd.returnType, uniqueIdDisplay)
        accMap + (fd -> new FunDef(freshId, fd.tparams, fd.params, fd.returnType))
      }
    }
    val mapExpr = mapFunctionsInExpr(funMap) _
    for ((from, to) <- funMap) {
      to.fullBody = if (!funToTmpl.contains(from)) {
        mapExpr {
          from.fullBody match {
            case Ensuring(b, post) =>
              Ensuring(b,
                Lambda(Seq(ValDef(getResId(from).get)),
                  createAnd(Seq(from.getPostWoTemplate, funToPost.getOrElse(from, tru)))))
            case fb =>
              fb
          }
        }
      } else {
        val newTmpl = createTemplateFun(funToTmpl(from))
        mapExpr {
          from.fullBody match {
            case Require(pre, body) =>
              val toPost =
                Lambda(Seq(ValDef(FreshIdentifier("res", from.returnType))),
                  createAnd(Seq(newTmpl, funToPost.getOrElse(from, tru))))
              Ensuring(Require(pre, body), toPost)

            case Ensuring(Require(pre, body), post) =>
              Ensuring(Require(pre, body),
                Lambda(Seq(ValDef(getResId(from).get)),
                  createAnd(Seq(from.getPostWoTemplate, newTmpl, funToPost.getOrElse(from, tru)))))

            case Ensuring(body, post) =>
              Ensuring(body,
                Lambda(Seq(ValDef(getResId(from).get)),
                  createAnd(Seq(from.getPostWoTemplate, newTmpl, funToPost.getOrElse(from, tru)))))

            case body =>
              val toPost =
                Lambda(Seq(ValDef(FreshIdentifier("res", from.returnType))),
                  createAnd(Seq(newTmpl, funToPost.getOrElse(from, tru))))
              Ensuring(body, toPost)
          }
        }
      }
      //copy annotations
      from.flags.foreach(to.addFlag(_))
    }
    val newprog = copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if funMap.contains(fd) =>
        funMap(fd)
      case d => d
    })
    newprog
  }

  def updatePost(funToPost: Map[FunDef, Lambda], prog: Program, uniqueIdDisplay: Boolean = true): Program = {

    val funMap = userLevelFunctions(prog).foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) =>
        val freshId = FreshIdentifier(fd.id.name, fd.returnType, uniqueIdDisplay)
        accMap + (fd -> new FunDef(freshId, fd.tparams, fd.params, fd.returnType))
    }
    val mapExpr = mapFunctionsInExpr(funMap) _
    for ((from, to) <- funMap) {
      to.fullBody = if (!funToPost.contains(from)) {
        mapExpr(from.fullBody)
      } else {
        val newpost = funToPost(from)
        mapExpr {
          from.fullBody match {
            case Ensuring(body, post) =>
              Ensuring(body, newpost) // replace the old post with new post
            case body =>
              Ensuring(body, newpost)
          }
        }
      }
      //copy annotations
      from.flags.foreach(to.addFlag(_))
    }
    val newprog = copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if funMap.contains(fd) =>
        funMap(fd)
      case d => d
    })
    newprog
  }

  def functionByName(nm: String, prog: Program) = {
    prog.definedFunctions.find(fd => fd.id.name == nm)
  }

  def functionByFullName(nm: String, prog: Program) = {
    prog.definedFunctions.find(fd => fullName(fd)(prog) == nm)
  }

  def functionsWOFields(fds: Seq[FunDef]): Seq[FunDef] = {
    fds.filter(fd => fd.isRealFunction)
  }

  /**
   * Functions that are not theory-operations or library methods that are not a part of the main unit
   */
  def userLevelFunctions(program: Program): Seq[FunDef] = {
    program.units.flatMap { u =>
      u.definedFunctions.filter(fd => !fd.isTheoryOperation && (u.isMainUnit || !(fd.isLibrary || fd.isInvariant)))
    }
  }

  def translateExprToProgram(ine: Expr, currProg: Program, newProg: Program): Expr = {
    var funCache = Map[String, Option[FunDef]]()
    def funInNewprog(fn: String) =
      funCache.get(fn) match {
        case None =>
          val fd = functionByFullName(fn, newProg)
          funCache += (fn -> fd)
          fd
        case Some(fd) => fd
      }
    simplePostTransform {
      case FunctionInvocation(TypedFunDef(fd, tps), args) =>
        val fname = fullName(fd)(currProg)
        funInNewprog(fname) match {
          case Some(nfd) =>
            FunctionInvocation(TypedFunDef(nfd, tps), args)
          case _ =>
            throw new IllegalStateException(s"Cannot find translation for ${fname}")
        }
      case e => e
    }(ine)
  }

  def getFunctionReturnVariable(fd: FunDef) = {
    if (fd.hasPostcondition) getResId(fd).get.toVariable
    else ResultVariable(fd.returnType) /*FreshIdentifier("res", fd.returnType).toVariable*/
  }

  def getResId(funDef: FunDef): Option[Identifier] = {
    funDef.fullBody match {
      case Ensuring(_, post) => {
        post match {
          case Lambda(Seq(ValDef(fromRes)), _) => Some(fromRes)
        }
      }
      case _ => None
    }
  }

  //compute the formal to the actual argument mapping
  def formalToActual(call: Call): Map[Expr, Expr] = {
    val fd = call.fi.tfd.fd
    val resvar = getFunctionReturnVariable(fd)
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ fd.params.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }
}

object PredicateUtil {
  /**
   * Returns a constructor for the let* and also the current
   * body of let*
   */
  def letStarUnapply(e: Expr): (Expr => Expr, Expr) = e match {
    case Let(binder, letv, letb) =>
      val (cons, body) = letStarUnapply(letb)
      (e => Let(binder, letv, cons(e)), body)
    case base =>
      (e => e, base)
  }

  def letStarUnapplyWithSimplify(e: Expr): (Expr => Expr, Expr) = {
    val (letCons, letBody) = letStarUnapply(e)
    (letCons andThen simplifyLets, letBody)
  }

  /**
   * Checks if the input expression has only template variables as free variables
   */
  def isTemplateExpr(expr: Expr): Boolean = {
    var foundVar = false
    postTraversal {
      case e @ Variable(id) =>
        if (!TemplateIdFactory.IsTemplateIdentifier(id))
          foundVar = true
      case e @ ResultVariable(_) =>
        foundVar = true
      case e =>
    }(expr)
    !foundVar
  }

  def isArithmeticRelation(e: Expr) = {
    e match {
      case Equals(l, r) =>
        if (l.getType == Untyped) None
        else Some(TypeUtil.isNumericType(l.getType))
      case _: LessThan | _: LessEquals | _: GreaterThan | _: GreaterEquals => Some(true)
      case _ => Some(false)
    }
  }

  def getTemplateIds(expr: Expr) = {
    variablesOf(expr).filter(TemplateIdFactory.IsTemplateIdentifier)
  }

  def getTemplateVars(expr: Expr): Set[Variable] = {
    getTemplateIds(expr).map(_.toVariable)
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasReals(expr: Expr): Boolean = {
    var foundReal = false
    postTraversal {
      case e if e.getType == RealType =>
          foundReal = true
      case _ =>
    }(expr)
    foundReal
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasRealsOrTemplates(expr: Expr): Boolean = {
    var found = false
    postTraversal {
      case Variable(id) if id.getType == RealType || TemplateIdFactory.IsTemplateIdentifier(id) =>
        found = true
      case e if e.getType == RealType =>
        found = true
      case _ =>
    }(expr)
    found
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   * Note: important, <, <=, > etc have default int type.
   * However, they can also be applied over real arguments
   * So check only if all terminals are real
   */
  def hasInts(expr: Expr): Boolean = {
    var foundInt = false
    postTraversal {
      case e: Terminal if (e.getType == Int32Type || e.getType == IntegerType) =>
        foundInt = true
      case _ =>
    }(expr)
    foundInt
  }

  def hasMixedIntReals(expr: Expr): Boolean = {
    hasInts(expr) && hasReals(expr)
  }

  /**
   * Assuming a flattenned formula
   */
  def atomNum(e: Expr): Int = e match {
    case And(args)         => (args map atomNum).sum
    case Or(args)          => (args map atomNum).sum
    case IfExpr(c, th, el) => atomNum(c) + atomNum(th) + atomNum(el)
    case Not(arg)          => atomNum(arg)
    case e                 => 1
  }

  def numUIFADT(e: Expr): Int = {
    var count: Int = 0
    simplePostTransform {
      case e @ (FunctionInvocation(_, _) | CaseClass(_, _) | Tuple(_)) => {
        count += 1
        e
      }
      case e => e
    }(e)
    count
  }

  def hasCalls(e: Expr) = numUIFADT(e) >= 1

  def getCallExprs(ine: Expr): Set[Expr] = {
    var calls = Set[Expr]()
    simplePostTransform((e: Expr) => e match {
      case call @ _ if isCallExpr(e) => {
        calls += e
        call
      }
      case _ => e
    })(ine)
    calls
  }

  def isCallExpr(e: Expr): Boolean = e match {
    case Equals(Variable(_), FunctionInvocation(_, _)) => true
    // case Iff(Variable(_),FunctionInvocation(_,_)) => true
    case _ => false
  }

  def isADTConstructor(e: Expr): Boolean = e match {
    case Equals(Variable(_), CaseClass(_, _)) => true
    case Equals(Variable(_), Tuple(_))        => true
    case _                                    => false
  }

  def isMultFunctions(fd: FunDef) = {
    (fd.id.name == "mult" || fd.id.name == "pmult") &&
      fd.isTheoryOperation
  }

  //replaces occurrences of mult by Times
  def multToTimes(ine: Expr): Expr = {
    simplePostTransform {
      case FunctionInvocation(TypedFunDef(fd, _), args) if isMultFunctions(fd) => {
        Times(args(0), args(1))
      }
      case e => e
    }(ine)
  }

  def createAnd(exprs: Seq[Expr]): Expr = {
    val newExprs = exprs.filterNot(conj => conj == tru)
    newExprs match {
      case Seq()  => tru
      case Seq(e) => e
      case _      => And(newExprs)
    }
  }

  def createOr(exprs: Seq[Expr]): Expr = {
    val newExprs = exprs.filterNot(disj => disj == fls)
    newExprs match {
      case Seq()  => fls
      case Seq(e) => e
      case _      => Or(newExprs)
    }
  }

  def precOrTrue(fd: FunDef): Expr = fd.precondition match {
    case Some(pre) => pre
    case None      => BooleanLiteral(true)
  }

  /**
   * Computes the set of variables that are shared across disjunctions.
   * This may return bound variables as well
   */
  def sharedIds(ine: Expr): Set[Identifier] = {

    def sharedOfDisjointExprs(args: Seq[Expr]) = {
      var uniqueVars = Set[Identifier]()
      var sharedVars = Set[Identifier]()
      args.foreach { arg =>
        val candUniques = variablesOf(arg) -- sharedVars
        val newShared = uniqueVars.intersect(candUniques)
        sharedVars ++= newShared
        uniqueVars = (uniqueVars ++ candUniques) -- newShared
      }
      sharedVars ++ (args flatMap rec)
    }
    def rec(e: Expr): Set[Identifier] =
      e match {
        case Or(args) => sharedOfDisjointExprs(args)
        case IfExpr(c, th, el) =>
          rec(c) ++ sharedOfDisjointExprs(Seq(th, el))
        case Variable(_) => Set()
        case Operator(args, op) =>
          (args flatMap rec).toSet
      }
    rec(ine)
  }
}
