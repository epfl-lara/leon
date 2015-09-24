package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Set => MutableSet, Map => MutableMap }
import scala.collection.immutable.Stack
import java.io._
import leon.invariant._
import java.io._
import solvers.z3._
import solvers._
import invariant.engine._
import invariant.factories._
import invariant.structure._
import leon.purescala.PrettyPrintable
import leon.purescala.PrinterContext
import purescala.PrinterHelpers._
import FunctionUtils._
import leon.invariant.templateSolvers.ExtendedUFSolver
import scala.annotation.tailrec

object FileCountGUID {
  var fileCount = 0
  def getID: Int = {
    var oldcnt = fileCount
    fileCount += 1
    oldcnt
  }
}

//three valued logic
object TVL {
  abstract class Value
  object FALSE extends Value
  object TRUE extends Value
  object MAYBE extends Value
}

//this is used as a place holder for result
case class ResultVariable(tpe: TypeTree) extends Expr with Terminal with PrettyPrintable {
  val getType = tpe
  override def toString: String = "#res"

  def printWith(implicit pctx: PrinterContext) {
    p"#res"
  }
}

//this used to refer to the time steps of a procedure
case class TimeVariable() extends Expr with Terminal with PrettyPrintable {
  val getType = IntegerType
  override def toString: String = "#time"
  def printWith(implicit pctx: PrinterContext) {
    p"#time"
  }
}

//this used to refer to the depth of a procedure
case class DepthVariable() extends Expr with Terminal with PrettyPrintable {
  val getType = IntegerType
  override def toString: String = "#depth"
  def printWith(implicit pctx: PrinterContext) {
    p"#time"
  }
}

object TVarFactory {

  val temporaries = MutableSet[Identifier]()
  //these are dummy identifiers used in 'CaseClassSelector' conversion
  val dummyIds = MutableSet[Identifier]()

  def createTemp(name: String, tpe: TypeTree = Untyped): Identifier = {
    val freshid = FreshIdentifier(name, tpe, true)
    temporaries.add(freshid)
    freshid
  }

  def createDummy(tpe: TypeTree): Identifier = {
    val freshid = FreshIdentifier("dy", tpe, true)
    dummyIds.add(freshid)
    freshid
  }

  def isTemporary(id: Identifier): Boolean = temporaries.contains(id)
  def isDummy(id: Identifier): Boolean = dummyIds.contains(id)
}

object Util {

  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)

  /**
   * Here, we exclude empty units that do not have any modules and empty
   * modules that do not have any definitions
   */
  def copyProgram(prog: Program, mapdefs: (Seq[Definition] => Seq[Definition])): Program = {
    prog.copy(units = prog.units.collect {
      case unit if (!unit.defs.isEmpty) => unit.copy(defs = unit.defs.collect {
        case module: ModuleDef if (!module.defs.isEmpty) =>
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
    val tmplFd = new FunDef(FreshIdentifier("tmpl", FunctionType(Seq(tmpl.getType), BooleanType), false), Seq(), Seq(ValDef(FreshIdentifier("arg", tmpl.getType),
            Some(tmpl.getType))), BooleanType)
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
        (if (isNumericType(fd.returnType)) Seq(Util.getFunctionReturnVariable(fd))
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
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(tfd, args) if funmap.contains(tfd.fd) =>
        FunctionInvocation(TypedFunDef(funmap(tfd.fd), tfd.tps), args)
      case _ => e
    })(ine)
  }

  def assignTemplateAndCojoinPost(funToTmpl: Map[FunDef, Expr], prog: Program,
      funToPost: Map[FunDef, Expr] = Map(), uniqueIdDisplay : Boolean = true): Program = {

    val funMap = Util.functionsWOFields(prog.definedFunctions).foldLeft(Map[FunDef, FunDef]()) {
      case (accMap, fd) if fd.isTheoryOperation =>
        accMap + (fd -> fd)
      case (accMap, fd) => {
        val freshId = FreshIdentifier(fd.id.name, fd.returnType, uniqueIdDisplay)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        accMap.updated(fd, newfd)
      }
    }

    // FIXME: This with createAnd (which performs simplifications) gives an error during composition.
    val mapExpr = mapFunctionsInExpr(funMap) _
    for ((from, to) <- funMap) {
      to.fullBody = if (!funToTmpl.contains(from)) {
        mapExpr {
          from.fullBody match {
            case Ensuring(b, post) =>
              Ensuring(b,
                Lambda(Seq(ValDef(Util.getResId(from).get)),
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
                Lambda(Seq(ValDef(Util.getResId(from).get)),
                  createAnd(Seq(from.getPostWoTemplate, newTmpl, funToPost.getOrElse(from, tru)))))

            case Ensuring(body, post) =>
              Ensuring(body,
                Lambda(Seq(ValDef(Util.getResId(from).get)),
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
    val newprog = Util.copyProgram(prog, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef if funMap.contains(fd) =>
        funMap(fd)
      case d => d
    })
    newprog
  }

  def functionByName(nm: String, prog: Program) = {
    prog.definedFunctions.find(fd => fd.id.name == nm)
  }

  def functionsWOFields(fds: Seq[FunDef]): Seq[FunDef] = {
    fds.filter(_.isRealFunction)
  }

  def isNumericExpr(expr: Expr): Boolean = {
    expr.getType == IntegerType ||
      expr.getType == RealType
  }

  def getFunctionReturnVariable(fd: FunDef) = {
    if (fd.hasPostcondition) getResId(fd).get.toVariable
    else ResultVariable(fd.returnType) /*FreshIdentifier("res", fd.returnType).toVariable*/
  }

  //compute the formal to the actual argument mapping
  def formalToActual(call: Call): Map[Expr, Expr] = {
    val fd = call.fi.tfd.fd
    val resvar = getFunctionReturnVariable(fd)
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ fd.params.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }

  /**
   * Checks if the input expression has only template variables as free variables
   */
  def isTemplateExpr(expr: Expr): Boolean = {
    var foundVar = false
    simplePostTransform((e: Expr) => e match {
      case Variable(id) => {
        if (!TemplateIdFactory.IsTemplateIdentifier(id))
          foundVar = true
        e
      }
      case ResultVariable(_) => {
        foundVar = true
        e
      }
      case _ => e
    })(expr)

    !foundVar
  }

  def getTemplateIds(expr: Expr) = {
    variablesOf(expr).filter(TemplateIdFactory.IsTemplateIdentifier)
  }

  def getTemplateVars(expr: Expr): Set[Variable] = {
    /*var tempVars = Set[Variable]()
    postTraversal(e => e match {
      case t @ Variable(id) =>
        if (TemplateIdFactory.IsTemplateIdentifier(id))
          tempVars += t
      case _ =>
    })(expr)
    tempVars*/
    getTemplateIds(expr).map(_.toVariable)
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasReals(expr: Expr): Boolean = {
    var foundReal = false
    simplePostTransform((e: Expr) => e match {
      case _ => {
        if (e.getType == RealType)
          foundReal = true;
        e
      }
    })(expr)
    foundReal
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   * Note: important, <, <=, > etc have default int type.
   * However, they can also be applied over real arguments
   * So check only if all terminals are real
   */
  def hasInts(expr: Expr): Boolean = {
    var foundInt = false
    simplePostTransform((e: Expr) => e match {
      case e: Terminal if (e.getType == Int32Type || e.getType == IntegerType) => {
        foundInt = true;
        e
      }
      case _ => e
    })(expr)
    foundInt
  }

  def hasMixedIntReals(expr: Expr): Boolean = {
    hasInts(expr) && hasReals(expr)
  }

  def fix[A](f: (A) => A)(a: A): A = {
    val na = f(a)
    if (a == na) a else fix(f)(na)
  }

  def atomNum(e: Expr): Int = {
    var count: Int = 0
    simplePostTransform((e: Expr) => e match {
      case And(args) => {
        count += args.size
        e
      }
      case Or(args) => {
        count += args.size
        e
      }
      case _ => e
    })(e)
    count
  }

  def numUIFADT(e: Expr): Int = {
    var count: Int = 0
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(_, _) | CaseClass(_, _) | Tuple(_) => {
        count += 1
        e
      }
      case _ => e
    })(e)
    count
  }

  def hasCalls(e: Expr) = numUIFADT(e) >= 1

  def getCallExprs(ine: Expr): Set[Expr] = {
    var calls = Set[Expr]()
    simplePostTransform((e: Expr) => e match {
      case call @ _ if Util.isCallExpr(e) => {
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
    case Equals(Variable(_), Tuple(_)) => true
    case _ => false
  }

  def modelToExpr(model: Model): Expr = {
    model.foldLeft(tru: Expr)((acc, elem) => {
      val (k, v) = elem
      val eq = Equals(k.toVariable, v)
      if (acc == tru) eq
      else And(acc, eq)
    })
  }

  def gcd(x: Int, y: Int): Int = {
    if (x == 0) y
    else gcd(y % x, x)
  }

  def toZ3SMTLIB(expr: Expr, filename: String,
    theory: String, ctx: LeonContext, pgm: Program,
    useBitvectors: Boolean = false,
    bitvecSize: Int = 32) = {
    //create new solver, assert constraints and print
    val printSol = new ExtendedUFSolver(ctx, pgm)
    printSol.assertCnstr(expr)
    val writer = new PrintWriter(filename)
    writer.println(printSol.ctrsToString(theory))
    printSol.free()
    writer.flush()
    writer.close()
  }

  /**
   * A helper function that can be used to hardcode an invariant and see if it unsatifies the paths
   */
  def checkInvariant(expr: Expr, ctx: LeonContext, prog: Program): Option[Boolean] = {
    val idmap: Map[Expr, Expr] = variablesOf(expr).collect {
      case id @ _ if (id.name.toString == "a?") => id.toVariable -> InfiniteIntegerLiteral(6)
      case id @ _ if (id.name.toString == "c?") => id.toVariable -> InfiniteIntegerLiteral(2)
    }.toMap
    //println("found ids: " + idmap.keys)
    if (!idmap.keys.isEmpty) {
      val newpathcond = replace(idmap, expr)
      //check if this is solvable
      val solver = SimpleSolverAPI(SolverFactory(() => new ExtendedUFSolver(ctx, prog)))
      solver.solveSAT(newpathcond)._1 match {
        case Some(true) => {
          println("Path satisfiable for a?,c? -->6,2 ")
          Some(true)
        }
        case _ => {
          println("Path unsat for a?,c? --> 6,2")
          Some(false)
        }
      }
    } else None
  }

  def collectUNSATCores(ine: Expr, ctx: LeonContext, prog: Program): Expr = {
    var controlVars = Map[Variable, Expr]()
    var newEqs = Map[Expr, Expr]()
    val solver = new ExtendedUFSolver(ctx, prog)
    val newe = simplePostTransform((e: Expr) => e match {
      case And(_) | Or(_) => {
        val v = TVarFactory.createTemp("a", BooleanType).toVariable
        newEqs += (v -> e)
        val newe = Equals(v, e)

        //create new variable and add it in disjunction
        val cvar = FreshIdentifier("ctrl", BooleanType, true).toVariable
        controlVars += (cvar -> newe)
        solver.assertCnstr(Or(newe, cvar))
        v
      }
      case _ => e
    })(ine)
    //create new variable and add it in disjunction
    val cvar = FreshIdentifier("ctrl", BooleanType, true).toVariable
    controlVars += (cvar -> newe)
    solver.assertCnstr(Or(newe, cvar))

    val res = solver.checkAssumptions(controlVars.keySet.map(Not.apply _))
    println("Result: " + res)
    val coreExprs = solver.getUnsatCore
    val simpcores = coreExprs.foldLeft(Seq[Expr]())((acc, coreExp) => {
      val Not(cvar @ Variable(_)) = coreExp
      val newexp = controlVars(cvar)
      //println("newexp: "+newexp)
      newexp match {
        // case Iff(v@Variable(_),rhs) if(newEqs.contains(v)) => acc
        case Equals(v @ Variable(_), rhs) if (v.getType == BooleanType && rhs.getType == BooleanType && newEqs.contains(v)) => acc
        case _ => {
          acc :+ newexp
        }
      }
    })
    val cores = Util.fix((e: Expr) => replace(newEqs, e))(Util.createAnd(simpcores.toSeq))

    solver.free
    //cores
    ExpressionTransformer.unFlatten(cores,
      variablesOf(ine).filterNot(TVarFactory.isTemporary _))
  }

  def isMultFunctions(fd: FunDef) = {
    (fd.id.name == "mult" || fd.id.name == "pmult") &&
      fd.isTheoryOperation
  }
  //replaces occurrences of mult by Times
  def multToTimes(ine: Expr): Expr = {
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(TypedFunDef(fd, _), args) if isMultFunctions(fd) => {
        Times(args(0), args(1))
      }
      case _ => e
    })(ine)
  }

  /**
   * A cross product with an optional filter
   */
  def cross[U, V](a: Set[U], b: Set[V], selector: Option[(U, V) => Boolean] = None): Set[(U, V)] = {

    val product = (for (x <- a; y <- b) yield (x, y))
    if (selector.isDefined)
      product.filter(pair => selector.get(pair._1, pair._2))
    else
      product
  }

  def getResId(funDef: FunDef): Option[Identifier] = {
    funDef.fullBody match {
      case Ensuring(_, post) => {
        post match {
          case Lambda(Seq(ValDef(fromRes, _)), _) => Some(fromRes)
          case _ =>
            throw new IllegalStateException("Postcondition with multiple return values!")
        }
      }
      case _ => None
    }
  }

  def createAnd(exprs: Seq[Expr]): Expr = {
    val newExprs = exprs.filterNot(conj => conj == tru)
    newExprs match {
      case Seq() => tru
      case Seq(e) => e
      case _ => And(newExprs)
    }
  }

  def createOr(exprs: Seq[Expr]): Expr = {
    val newExprs = exprs.filterNot(disj => disj == fls)
    newExprs match {
      case Seq() => fls
      case Seq(e) => e
      case _ => Or(newExprs)
    }
  }

  def isNumericType(t: TypeTree) = t match {
    case IntegerType | RealType => true
    case _ => false
  }

  //tests if the solver uses nlsat
  def usesNLSat(solver: AbstractZ3Solver) = {
    //check for nlsat
    val x = FreshIdentifier("x", RealType).toVariable
    val testExpr = Equals(Times(x, x), FractionalLiteral(2, 1))
    solver.assertCnstr(testExpr)
    solver.check match {
      case Some(true) => true
      case _ => false
    }
  }

  def matchToITE(ine: Expr) = {
    val liftedExpr = simplePostTransform {
      case me @ MatchExpr(scrut, cases) => scrut match {
        case t: Terminal => me
        case _ => {
          val freshid = FreshIdentifier("m", scrut.getType, true)
          Let(freshid, scrut, MatchExpr(freshid.toVariable, cases))
        }
      }
      case e => e
    }(ine)
    purescala.ExprOps.matchToIfThenElse(liftedExpr)
  }

  def precOrTrue(fd: FunDef): Expr = fd.precondition match {
    case Some(pre) => pre
    case None => BooleanLiteral(true)
  }

  /*
   * Apply an expression operation on all expressions contained in a FunDef
   */
  def applyOnFunDef(operation: Expr => Expr)(funDef: FunDef): FunDef = {
    val newFunDef = funDef.duplicate
    newFunDef.fullBody = operation(funDef.fullBody)
    newFunDef
  }

  /**
   * Apply preMap on all expressions contained in a FunDef
   */
  def preMapOnFunDef(repl: Expr => Option[Expr], applyRec: Boolean = false)(funDef: FunDef): FunDef = {
    applyOnFunDef(preMap(repl, applyRec))(funDef)
  }

  /**
   * Apply postMap on all expressions contained in a FunDef
   */
  def postMapOnFunDef(repl: Expr => Option[Expr], applyRec: Boolean = false)(funDef: FunDef): FunDef = {
    applyOnFunDef(postMap(repl, applyRec))(funDef)
  }
}

/**
 * maps all real valued variables and literals to new integer variables/literals and
 * performs the reverse mapping
 * Note: this should preserve the template identifier property
 */
class RealToInt {

  val bone = BigInt(1)
  var realToIntId = Map[Identifier, Identifier]()
  var intToRealId = Map[Identifier, Identifier]()

  def mapRealToInt(inexpr: Expr): Expr = {
    val transformer = (e: Expr) => e match {
      case FractionalLiteral(num, `bone`) => InfiniteIntegerLiteral(num)
      case FractionalLiteral(_, _) => throw new IllegalStateException("Real literal with non-unit denominator")
      case v @ Variable(realId) if (v.getType == RealType) => {
        val newId = realToIntId.getOrElse(realId, {
          //note: the fresh identifier has to be a template identifier if the original one is a template identifier
          val freshId = if (TemplateIdFactory.IsTemplateIdentifier(realId))
            TemplateIdFactory.freshIdentifier(realId.name, IntegerType)
          else
            FreshIdentifier(realId.name, IntegerType, true)

          realToIntId += (realId -> freshId)
          intToRealId += (freshId -> realId)
          freshId
        })
        Variable(newId)
      }
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }

  def unmapModel(model: Model): Model = {
    new Model(model.map(pair => {
      val (key, value) = if (intToRealId.contains(pair._1)) {
        (intToRealId(pair._1),
          pair._2 match {
            case InfiniteIntegerLiteral(v) => FractionalLiteral(v.toInt, 1)
            case _ => pair._2
          })
      } else pair
      (key -> value)
    }).toMap)
  }

  def mapModel(model: Model): Model = {
    new Model(model.collect {
      case (k, FractionalLiteral(n, bone)) =>
        (realToIntId(k), InfiniteIntegerLiteral(n))
      case (k, v) =>
        if (realToIntId.contains(k)) {
          (realToIntId(k), v)
        } else {
          (k, v)
        }
    }.toMap)
  }
}

class MultiMap[A, B] extends scala.collection.mutable.HashMap[A, scala.collection.mutable.Set[B]] with scala.collection.mutable.MultiMap[A, B] {
  /**
   * Creates a new map and does not change the existing map
   */
  def append(that: MultiMap[A, B]): MultiMap[A, B] = {
    val newmap = new MultiMap[A, B]()
    this.foreach { case (k, vset) => newmap += (k -> vset) }
    that.foreach {
      case (k, vset) => vset.foreach(v => newmap.addBinding(k, v))
    }
    newmap
  }
}

/**
 * A multimap that allows duplicate entries
 */
class OrderedMultiMap[A, B] extends scala.collection.mutable.HashMap[A, scala.collection.mutable.ListBuffer[B]] {

  def addBinding(key: A, value: B): this.type = {
    get(key) match {
      case None =>
        val list = new scala.collection.mutable.ListBuffer[B]()
        list += value
        this(key) = list
      case Some(list) =>
        list += value
    }
    this
  }

  /**
   * Creates a new map and does not change the existing map
   */
  def append(that: OrderedMultiMap[A, B]): OrderedMultiMap[A, B] = {
    val newmap = new OrderedMultiMap[A, B]()
    this.foreach { case (k, vlist) => newmap += (k -> vlist) }
    that.foreach {
      case (k, vlist) => vlist.foreach(v => newmap.addBinding(k, v))
    }
    newmap
  }

  /**
   * Make the value of every key distinct
   */
  def distinct: OrderedMultiMap[A, B] = {
    val newmap = new OrderedMultiMap[A, B]()
    this.foreach { case (k, vlist) => newmap += (k -> vlist.distinct) }
    newmap
  }
}

/**
 * Implements a mapping from Seq[A] to B where Seq[A]
 * is stored as a Trie
 */
final class TrieMap[A, B] {
  var childrenMap = Map[A, TrieMap[A, B]]()
  var dataMap = Map[A, B]()

  @tailrec def addBinding(key: Seq[A], value: B) {
    key match {
      case Seq() =>
        throw new IllegalStateException("Key is empty!!")
      case Seq(x) =>
        //add the value to the dataMap
        if (dataMap.contains(x))
          throw new IllegalStateException("A mapping for key already exists: " + x + " --> " + dataMap(x))
        else
          dataMap += (x -> value)
      case head +: tail => //here, tail has at least one element
        //check if we have an entry for seq(0) if yes go to the children, if not create one
        val child = childrenMap.getOrElse(head, {
          val ch = new TrieMap[A, B]()
          childrenMap += (head -> ch)
          ch
        })
        child.addBinding(tail, value)
    }
  }

  @tailrec def lookup(key: Seq[A]): Option[B] = {
    key match {
      case Seq() =>
        throw new IllegalStateException("Key is empty!!")
      case Seq(x) =>
        dataMap.get(x)
      case head +: tail => //here, tail has at least one element
        childrenMap.get(head) match {
          case Some(child) =>
            child.lookup(tail)
          case _ => None
        }
    }
  }
}

class CounterMap[T] extends scala.collection.mutable.HashMap[T, Int] {
  def inc(v: T) = {
    if (this.contains(v))
      this(v) += 1
    else this += (v -> 1)
  }
}

/**
 * A class that looks for structural equality of expressions
 * by ignoring the variable names.
 * Useful for factoring common parts of two expressions into functions.
 */
class ExprStructure(val e: Expr) {
  def structurallyEqual(e1: Expr, e2: Expr): Boolean = {
    (e1, e2) match {
      case (t1: Terminal, t2: Terminal) =>
        // we need to specially handle type parameters as they are not considered equal by default
        (t1.getType, t2.getType) match {
          case (ct1: ClassType, ct2: ClassType) =>
            if (ct1.classDef == ct2.classDef && ct1.tps.size == ct2.tps.size) {
              (ct1.tps zip ct2.tps).forall {
                case (TypeParameter(_), TypeParameter(_)) =>
                  true
                case (a, b) =>
                  println(s"Checking Type arguments: $a, $b")
                  a == b
              }
            } else false
          case (ty1, ty2) => ty1 == ty2
        }
      case (Operator(args1, op1), Operator(args2, op2)) =>
        (op1 == op2) && (args1.size == args2.size) && (args1 zip args2).forall {
          case (a1, a2) => structurallyEqual(a1, a2)
        }
      case _ =>
        false
    }
  }

  override def equals(other: Any) = {
    other match {
      case other: ExprStructure =>
        structurallyEqual(e, other.e)
      case _ =>
        false
    }
  }

  override def hashCode = {
    var opndcount = 0 // operand count
    var opcount = 0 // operator count
    postTraversal {
      case t: Terminal => opndcount += 1
      case _ => opcount += 1
    }(e)
    (opndcount << 16) ^ opcount
  }
}

object TypeUtil {
  def getTypeParameters(t: TypeTree): Seq[TypeParameter] = {
    t match {
      case tp @ TypeParameter(_) => Seq(tp)
      case NAryType(tps, _) =>
        (tps flatMap getTypeParameters).distinct
    }
  }

  def typeNameWOParams(t: TypeTree): String = t match {
    case ct: ClassType => ct.id.name
    case TupleType(ts) => ts.map(typeNameWOParams).mkString("(", ",", ")")
    case ArrayType(t) => s"Array[${typeNameWOParams(t)}]"
    case SetType(t) => s"Set[${typeNameWOParams(t)}]"
    case MapType(from, to) => s"Map[${typeNameWOParams(from)}, ${typeNameWOParams(to)}]"
    case FunctionType(fts, tt) =>
      val ftstr = fts.map(typeNameWOParams).mkString("(", ",", ")")
      s"$ftstr => ${typeNameWOParams(tt)}"
    case t => t.toString
  }

  def instantiateTypeParameters(tpMap: Map[TypeParameter, TypeTree])(t: TypeTree): TypeTree = {
    t match {
      case tp: TypeParameter => tpMap.getOrElse(tp, tp)
      case NAryType(subtypes, tcons) =>
        tcons(subtypes map instantiateTypeParameters(tpMap) _)
    }
  }

  /**
   * `gamma` is the initial type environment which has
   * type bindings for free variables of `ine`.
   * It is not necessary that gamma should match the types of the
   * identifiers of the free variables.
   * Set and Maps are not supported yet
   */
  def inferTypesOfLocals(ine: Expr, initGamma: Map[Identifier, TypeTree]): Expr = {
    var idmap = Map[Identifier, Identifier]()
    var gamma = initGamma

    /**
     * Note this method has side-effects
     */
    def makeIdOfType(oldId: Identifier, tpe: TypeTree): Identifier = {
      if (oldId.getType != tpe) {
        val freshid = FreshIdentifier(oldId.name, tpe, true)
        idmap += (oldId -> freshid)
        gamma += (oldId -> tpe)
        freshid
      } else oldId
    }

    def rec(e: Expr): (TypeTree, Expr) = {
      val res = e match {
        case Let(id, value, body) =>
          val (valType, nval) = rec(value)
          val nid = makeIdOfType(id, valType)
          val (btype, nbody) = rec(body)
          (btype, Let(nid, nval, nbody))

        case Ensuring(body, Lambda(Seq(resdef @ ValDef(resid, _)), postBody)) =>
          val (btype, nbody) = rec(body)
          val nres = makeIdOfType(resid, btype)
          (btype, Ensuring(nbody, Lambda(Seq(ValDef(nres)), rec(postBody)._2)))

        case MatchExpr(scr, mcases) =>
          val (scrtype, nscr) = rec(scr)
          val ncases = mcases.map {
            case MatchCase(pat, optGuard, rhs) =>
              // resetting the type of patterns in the matches
              def mapPattern(p: Pattern, expType: TypeTree): (Pattern, TypeTree) = {
                p match {
                  case InstanceOfPattern(bopt, ict) =>
                    // choose the subtype of the `expType` that
                    // has the same constructor as `ict`
                    val ntype = subcast(ict, expType.asInstanceOf[ClassType])
                    if (!ntype.isDefined)
                      throw new IllegalStateException(s"Cannot find subtype of $expType with name: ${ict.classDef.id.toString}")
                    val nbopt = bopt.map(makeIdOfType(_, ntype.get))
                    (InstanceOfPattern(nbopt, ntype.get), ntype.get)

                  case CaseClassPattern(bopt, ict, subpats) =>
                    val ntype = subcast(ict, expType.asInstanceOf[ClassType])
                    if (!ntype.isDefined)
                      throw new IllegalStateException(s"Cannot find subtype of $expType with name: ${ict.classDef.id.toString}")
                    val cct = ntype.get.asInstanceOf[CaseClassType]
                    val nbopt = bopt.map(makeIdOfType(_, cct))
                    val npats = (subpats zip cct.fieldsTypes).map {
                      case (p, t) =>
                        //println(s"Subpat: $p expected type: $t")
                        mapPattern(p, t)._1
                    }
                    (CaseClassPattern(nbopt, cct, npats), cct)

                  case TuplePattern(bopt, subpats) =>
                    val TupleType(subts) = scrtype
                    val patnTypes = (subpats zip subts).map {
                      case (p, t) => mapPattern(p, t)
                    }
                    val npats = patnTypes.map(_._1)
                    val ntype = TupleType(patnTypes.map(_._2))
                    val nbopt = bopt.map(makeIdOfType(_, ntype))
                    (TuplePattern(nbopt, npats), ntype)

                  case WildcardPattern(bopt) =>
                    val nbopt = bopt.map(makeIdOfType(_, expType))
                    (WildcardPattern(nbopt), expType)

                  case LiteralPattern(bopt, lit) =>
                    val ntype = lit.getType
                    val nbopt = bopt.map(makeIdOfType(_, ntype))
                    (LiteralPattern(nbopt, lit), ntype)
                  case _ =>
                    throw new IllegalStateException("Not supported yet!")
                }
              }
              val npattern = mapPattern(pat, scrtype)._1
              val nguard = optGuard.map(rec(_)._2)
              val nrhs = rec(rhs)._2
              //println(s"New rhs: $nrhs inferred type: ${nrhs.getType}")
              MatchCase(npattern, nguard, nrhs)
          }
          val nmatch = MatchExpr(nscr, ncases)
          (nmatch.getType, nmatch)

        case cs @ CaseClassSelector(cltype, clExpr, fld) =>
          val (ncltype: CaseClassType, nclExpr) = rec(clExpr)
          (ncltype, CaseClassSelector(ncltype, nclExpr, fld))

        case AsInstanceOf(clexpr, cltype) =>
          val (ncltype: ClassType, nexpr) = rec(clexpr)
          subcast(cltype, ncltype) match {
            case Some(ntype) => (ntype, AsInstanceOf(nexpr, ntype))
            case _ =>
              //println(s"asInstanceOf type of $clExpr is: $cltype inferred type of $nclExpr : $ct")
              throw new IllegalStateException(s"$nexpr : $ncltype cannot be cast to case class type: $cltype")
          }

        case v @ Variable(id) =>
          if (gamma.contains(id)) {
            if (idmap.contains(id))
              (gamma(id), idmap(id).toVariable)
            else {
              (gamma(id), v)
            }
          } else (id.getType, v)

        // need to handle tuple select specially
        case TupleSelect(tup, i) =>
          val nop = TupleSelect(rec(tup)._2, i)
          (nop.getType, nop)
        case Operator(args, op) =>
          val nop = op(args.map(arg => rec(arg)._2))
          (nop.getType, nop)
        case t: Terminal =>
          (t.getType, t)
      }
      //println(s"Inferred type of $e : ${res._1} new expression: ${res._2}")
      if (res._1 == Untyped) {
        throw new IllegalStateException(s"Cannot infer type for expression: $e")
      }
      res
    }

    def subcast(oldType: ClassType, newType: ClassType): Option[ClassType] = {
      newType match {
        case AbstractClassType(absClass, tps) if absClass.knownCCDescendants.contains(oldType.classDef) =>
          //here oldType.classDef <: absClass
          Some(CaseClassType(oldType.classDef.asInstanceOf[CaseClassDef], tps))
        case cct: CaseClassType =>
          Some(cct)
        case _ =>
          None
      }
    }
    rec(ine)._2
  }
}