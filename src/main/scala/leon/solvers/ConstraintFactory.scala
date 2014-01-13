package leon
package solvers

import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.HOTreeOps._
import purescala.Extractors._
import purescala.Definitions._
import purescala.Common._


class ConstraintFactory[T](templateFactory: TemplateFactory[T]) {

  private type Call = (FunctionApplication, Map[Identifier, T])
  private class CallMap(calls: Map[Identifier, Seq[Call]]) {
    def this() = this(Map())

    private def get(key: Identifier): Seq[Call] = calls.getOrElse(key, Seq())
    private def id(expr: Expr): Identifier = expr match {
      case FunctionApplication(caller, args) => id(caller)
      case Variable(id) => id
      case error => scala.sys.error("CallMap shouldn't contain " + error + " callers")
    }

    def keys = calls.keys

    def merge(that: CallMap): CallMap = new CallMap({
      (keys ++ that.keys).map(key => key -> (get(key) ++ that.get(key))).toMap
    })

    def +(id: Identifier, call: Call): CallMap = new CallMap({
      calls updated (id, get(id) :+ call)
    })

    def +(id: Identifier, f: FunctionApplication, idSubstMap: Map[Identifier, T]): CallMap = {
      val callVarMapping = variablesOf(f).filter(!_.getType.isInstanceOf[FunctionType]).map(id => id -> id.freshen).toMap
      val callVarSubst = callVarMapping.map(p => p._2 -> idSubstMap(p._1))
      val call = replaceFromIDs(callVarMapping.mapValues(_.toVariable), f).asInstanceOf[FunctionApplication] -> callVarSubst
      this + (id, call)
    }

    def ++(that: CallMap): CallMap = this merge that

    def canFill(id: Identifier)(count: Int): Boolean = get(id).size >= count
    def canFill(application: FunctionApplication)(count: Int): Boolean = canFill(id(application))(count)

    def fill(id: Identifier): Seq[Call] = get(id)
    def fill(application: FunctionApplication): Seq[Call] = fill(id(application))

    override def toString: String = "CallMap: \n  " + calls.mkString("\n  ")
  }

  private var calls : CallMap = new CallMap()

  def reset() {
    calls = new CallMap()
  }

  private val forallVars : Set[Identifier] = templateFactory.precondition match {
    case And(es) => es.collect { case ForallExpression(args, _) => args.map(_.id) }.flatten.toSet
    case ForallExpression(args, _) => args.map(_.id).toSet
    case _ => Set.empty
  }

  private val argumentIDs : Set[Identifier] = variablesOf(templateFactory.precondition) -- forallVars

  private val precondition = postMap({
    case IfExpr(cond, thenn, elze) => Some(And(Implies(cond, thenn), Implies(Not(cond), elze)))
    case ForallExpression(args, body) => Some(body)
    case _ => None
  })(expandLets(templateFactory.precondition))

  def required(expr: Expr, idSubstMap: Map[Identifier, T]) : (Seq[Expr], Map[Identifier, T]) = {
    var constraints   : Seq[Expr]          = Seq()
    var newIdSubstMap : Map[Identifier, T] = Map()

    def extract(f: FunctionApplication) : Option[(Identifier, FunctionApplication)] = app2Caller(f) match {
      case VariableCaller(id) if !forallVars(id) => Some(id -> f)
      case _ => None
    }

    def visitArguments(args: Seq[Expr], calls: CallMap, newCalls: CallMap) = args.foldLeft(newCalls) {
      case (accCalls, arg) => accCalls merge visit(arg, calls merge accCalls)
    }

    def visitApp(app: Expr, calls: CallMap, partial: PartialFunction[Expr, CallMap]): CallMap = {
      val recurse : PartialFunction[Expr, CallMap] = { case FunctionApplication(c, args) =>
        val appCalls = visitApp(c, calls, partial)
        val argCalls = visitArguments(args, calls, appCalls)
        appCalls merge argCalls
      }
      val apply = recurse orElse partial
      apply(app)
    }

    def visit(expr: Expr, calls: CallMap): CallMap = expr match {
      case IfExpr(cond, thenn, elze) => {
        val condCalls = visit(cond, calls)
        val thenCalls = visit(thenn, calls merge condCalls)
        val elseCalls = visit(elze, calls merge condCalls)
        condCalls merge thenCalls merge elseCalls
      }
      case AnonymousFunction(_, _) => calls
      case f @ FunctionApplication(caller, args) => app2Caller(f) match {
        case AnonymousCaller(a) =>
          sys.error("Shouldn't encounter AnonymousFunctions during constraint building")

        case InvocationCaller(fd) =>
          visitApp(f, calls, { case FunctionInvocation(fd, args) => visitArguments(args, calls, new CallMap()) })

        case VariableCaller(id) =>
          val appCalls = visitApp(f, calls, { case Variable(id) => new CallMap() })
          val allCalls = calls merge appCalls
          val allSubsts = idSubstMap ++ newIdSubstMap
          val (newConstraints, newSubsts, newExpressions) = generateCallConstraints(app2ID(f), f, precondition, allCalls, allSubsts, extract)
            
          constraints ++= newConstraints
          newIdSubstMap ++= newSubsts

          newExpressions.foldLeft(appCalls + (id, f, idSubstMap ++ newIdSubstMap)) { case (accCalls, expr) =>
            accCalls merge visit(expr, calls merge accCalls)
          }
      }
      case NAryOperator(args, recons) => {
        args.foldLeft(new CallMap())({ case (accCalls, arg) => accCalls merge visit(arg, calls merge accCalls) })
      }
      case BinaryOperator(e1, e2, recons) => {
        val e1Calls = visit(e1, calls)
        e1Calls merge visit(e2, calls merge e1Calls)
      }
      case UnaryOperator(e, recons) => {
        visit(e, calls)
      }
      case t: Terminal => {
        new CallMap()
      }
      case _ => scala.sys.error("Expression " + expr + " shouldn't be encountered in buildCallMap.rec")
    }

    calls ++= visit(preProcess(expr), calls)
    (constraints, newIdSubstMap)
  }

  def assumed(application: FunctionApplication, idSubstMap: Map[Identifier, T]) : (Seq[Expr], Map[Identifier, T]) = {
    def invocation(app: Expr): FunctionInvocation = app match {
      case FunctionApplication(f, _) => invocation(f)
      case fi @ FunctionInvocation(_, _) => fi
      case _ => scala.sys.error("Unexpected argument to invocation extractor : " + app)
    }

    val fi @ FunctionInvocation(fd, args) = invocation(application)

    fd.postcondition.map { case (resID, condition) =>
      def extract(f: FunctionApplication) : Option[(Identifier, FunctionApplication)] = app2Caller(f) match {
        case VariableCaller(id) if id == resID => Some(id -> replaceFromIDs(Map(resID -> fi), f).asInstanceOf[FunctionApplication])
        case _ => None
      }

      val postcondition = replaceFromIDs(Map(fd.args.map(_.id) zip args : _*), condition)
      val (newConstraints, newSubsts, newExpressions) = generateCallConstraints(resID, application, postcondition, calls, idSubstMap, extract)
      val mappedConstraints = newConstraints.map(expr => replaceFromIDs(Map(resID -> fi), expr))

      calls += (resID, application, idSubstMap ++ newSubsts)

      val exprs = newExpressions :+ replaceFromIDs(Map(resID -> fi), postcondition)
      exprs.foldLeft(mappedConstraints -> newSubsts) { case ((cstrs, subst), expr) =>
        val allSubst = idSubstMap ++ subst
        val (newConstraints, newSubsts) = required(expr, allSubst)
        (cstrs ++ newConstraints, subst ++ newSubsts)
      }
    }.getOrElse(Seq(), Map())
  }

  type AppExtractor = FunctionApplication => Option[(Identifier, FunctionApplication)]

  private def generateCallConstraints(id           : Identifier,
                                      application  : FunctionApplication,
                                      condition    : Expr,
                                      calls        : CallMap,
                                      idSubstMap   : Map[Identifier, T],
                                      extractor    : AppExtractor) = {

    var constraints    : Seq[Expr]          = Seq.empty
    var newExpressions : Seq[Expr]          = Seq.empty
    var newIdSubstMap  : Map[Identifier, T] = Map.empty

    val nonFree : Set[Identifier] = argumentIDs ++ Set(id)

    def applicationEqualityConstraints(app1: FunctionApplication, app2: FunctionApplication): Seq[(Expr,Expr)] = {
      (app1.args zip app2.args) ++ ((app1.function, app2.function) match {
        case (Variable(i1), Variable(i2)) if i1 == i2 => Seq()
        case (FunctionInvocation(fd1, args1), FunctionInvocation(fd2, args2)) if fd1 == fd2 => args1 zip args2
        case (f1 @ FunctionApplication(_, _), f2 @ FunctionApplication(_, _)) => applicationEqualityConstraints(f1, f2)
        case _ => sys.error("Shouldn't encounter (" + app1.function + "," + app2.function + ") in applicationEqualityConstraints")
      })
    }

    def freeBindingEqualityConstraints(constraints: Seq[(Expr, Expr)]) = {
      def rec(grouped: Seq[(Set[Identifier], Seq[Expr])], count: Int, bound: Set[Identifier]): (Expr, Expr) = {
        val (current, next) = grouped.partition(_._1.size == count)
        val (newBound, hard, soft) = current.foldLeft(bound, Seq[Expr](), Seq[Expr]()) {
          case ((bound, hard, soft), (vars, seq)) =>
            if ((vars -- bound).nonEmpty)
              (bound ++ vars, hard :+ seq.head, soft ++ seq.tail)
            else
              (bound, hard, soft ++ seq)
        }

        if(next.nonEmpty) {
          val (nextHard, nextSoft) = rec(next, count + 1, newBound)
          (And(hard :+ nextHard), And(soft :+ nextSoft))
        } else {
          (And(hard), And(soft))
        }
      }

      val grouped = constraints.groupBy({
        case (general, real) => variablesOf(general) -- nonFree
      }).mapValues({ seq =>
        // seq elements are of the shape (abstract expression, concrete expression)
        val sorted = seq.sortBy(p => formulaSize(p._1))
        sorted.map(p => Equals(p._1, p._2))
      }).toSeq

      rec(grouped, 0, Set())
    }

    def mappingToConstraint(condition: Expr, mapping: Map[FunctionApplication, FunctionApplication]) {
      val argumentConstraints : Seq[(Expr, Expr)] = mapping.iterator.map {
        case (template, instance) => applicationEqualityConstraints(template, instance)
      }.flatten.toSeq

      val (abstractHOConstraints, otherConstraints) = argumentConstraints.partition {
        case (Variable(id), instance) => forallVars(id) && id.getType.isInstanceOf[FunctionType]
        case _ => false
      }

      if (abstractHOConstraints.isEmpty) {
        val (hardConstraints, softConstraints) = freeBindingEqualityConstraints(otherConstraints)
        val constraint = And(hardConstraints, Implies(softConstraints, condition))
        constraints :+= constraint
      } else {
        // prepare to generate abstract HO variable replacement mapping
        val abstractHOToInstanceSet = abstractHOConstraints.groupBy(_._1).mapValues(_.map(_._2))

        // if we have an abstract HO variable that maps to two different values, disregard constraint
        if (abstractHOToInstanceSet.forall(_._2.toList match {
          case x :: xs => xs.forall(x2 => templateFactory.lambdaEquals(x, x2, idSubstMap ++ newIdSubstMap))
          case _ => true
        })) {
          // perform abstract HO variable replacement
          val abstractHOMap : Map[Expr, Expr] = abstractHOToInstanceSet.mapValues(_.head).toMap

          val mappedExpr = applyAnonymous(replace(abstractHOMap, condition))
          val mappedMapping = mapping.map(p => (applyAnonymous(replace(abstractHOMap, p._1)).asInstanceOf[FunctionApplication], p._2))

          mappingToConstraint(mappedExpr, mappedMapping)

          newExpressions ++= (mapping.map(p => p._1).toSeq :+ condition).flatMap { expr =>
            def caller(app: FunctionApplication): Option[Expr] = app.function match {
              case (fa : FunctionApplication) => caller(fa)
              case expr @ Variable(id) => Some(expr)
              case _ => None
            }

            def visit(expr: Expr, args_only: Boolean): Seq[Expr] = expr match {
              case fa @ FunctionApplication(c, args) if !args_only => caller(fa) match {
                case Some(expr) if abstractHOMap.contains(expr) =>
                  val applied = applyAnonymous(replace(abstractHOMap, fa))
                  Seq(applied) ++ visit(fa, true)
                case _ => visit(c, args_only) ++ args.flatMap(visit(_, args_only))
              }
              case NAryOperator(es, _) => es.flatMap(visit(_, args_only))
              case BinaryOperator(e1, e2, _) => visit(e1, args_only) ++ visit(e2, args_only)
              case UnaryOperator(e1, _) => visit(e1, args_only)
              case _ => Seq.empty
            }

            visit(expr, false)
          }
        }
      }
    }

    def applicationsToConstraints(condition: Expr, replacements: Map[Identifier, Set[FunctionApplication]]) {
      val functions = replacements.values.flatten.toSet

      for (replacedByApplication <- replacements(id)) {
        // Generate all mappings where at least one function is replaced by the application we are constraining ...
        val fillings    : Seq[Seq[(FunctionApplication, Call)]] = (functions - replacedByApplication).toSeq.map(f => calls.fill(f).map(f -> _))
        val initMapping : Seq[Map[FunctionApplication, Call]]   = Seq(Map(replacedByApplication -> (application -> Map())))

        // here the mapping generation takes place. We convert our list of sets of mappings (there is one set
        // per function variable into a list of mappings by cartesian product (again, empty mapping for current application)
        val allMappings : Seq[Map[FunctionApplication, Call]]   = fillings.foldLeft(initMapping) { (acc, app2calls) =>
          app2calls.map { case (fa, call) =>
            // each previous call can only be assigned once in the constraint, so mappings containing multiple assignments
            // of the same call must be filtered out
            acc.map(map => if (map.values.exists(_ == call)) None else Some(map + (fa -> call))).flatten
          }.flatten
        }

        // Use each possible mapping to build constraints (which ones are real will be determined by the solver)
        for (mapping <- allMappings) {
          newIdSubstMap ++= mapping.flatMap(entry => entry._2._2)

          // function arguments are NOT free variables and should not be freshened!
          val freeVars : Set[Identifier] = forallVars.filter(!_.getType.isInstanceOf[FunctionType])
          val forallVarsMap : Map[Identifier, Identifier] = freeVars.map(id => id -> id.freshen).toMap
          newIdSubstMap ++= forallVarsMap.values.map(id => id -> templateFactory.encode(id))

          val subst : Map[Identifier, Expr] = forallVarsMap.mapValues(_.toVariable)
          val freshMapping = mapping.map(p => replaceFromIDs(subst, p._1).asInstanceOf[FunctionApplication] -> p._2._1)
          val freshCondition = replaceFromIDs(subst, condition)

          mappingToConstraint(freshCondition, freshMapping)
        }
      }
    }

    object Instantiable {
      def unapply(expr: Expr): Option[Map[Identifier, Set[FunctionApplication]]] = {
        def extract(expr: Expr) : Set[(Identifier, FunctionApplication)] = expr match {
          case AnonymousFunction(_, _) => Set()
          case f @ FunctionApplication(caller, args) => extract(caller) ++ args.flatMap(extract) ++ extractor(f)
          case NAryOperator(es, _) => es.flatMap(extract).toSet
          case BinaryOperator(e1, e2, _) => extract(e1) ++ extract(e2)
          case UnaryOperator(e, _) => extract(e)
          case (_ : Terminal) => Set()
        }

        val applications = extract(expr)
        val id2application = applications.groupBy(_._1).mapValues(_.map(_._2))
        if (id2application.contains(id) && id2application.keys.forall { i =>
          if (i != id) calls.canFill(i)(id2application(i).size) else calls.canFill(i)(id2application(i).size - 1)
        }) Some(id2application) else None
      }
    }

    condition match {
      // And operators are flattened at construction so we won't miss anything by requiring instantiable children
      case And(es) => for (expr @ Instantiable(applications) <- es) applicationsToConstraints(expr, applications)
      // We make sure all other operators need to be complete to be considerable as conditions
      case expr @ Instantiable(applications) => applicationsToConstraints(expr, applications)
      case e if e.getType == BooleanType =>
    }

    (constraints, newIdSubstMap, newExpressions)
  }
}


// vim: set ts=4 sw=4 et:
