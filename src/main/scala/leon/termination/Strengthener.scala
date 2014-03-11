package leon
package termination

import purescala.Trees._
import purescala.TypeTrees._
import purescala.TreeOps._
import purescala.Common._
import purescala.Definitions._

import scala.collection.mutable.{Set => MutableSet, Map => MutableMap}

trait Strengthener { self : TerminationChecker with RelationComparator with RelationBuilder =>

  private val strengthenedPost : MutableSet[FunDef] = MutableSet.empty

  def strengthenPostconditions(funDefs: Set[FunDef])(implicit solver: Processor with Solvable) {
    // Strengthen postconditions on all accessible functions by adding size constraints
    val callees : Set[FunDef] = funDefs.map(fd => self.program.callGraph.transitiveCallees(fd)).flatten
    val sortedCallees : Seq[FunDef] = callees.toSeq.sortWith((fd1, fd2) => self.program.callGraph.transitivelyCalls(fd2, fd1))

    for (funDef <- sortedCallees if !strengthenedPost(funDef) && funDef.hasBody && self.terminates(funDef).isGuaranteed) {
      def strengthen(cmp: (Expr, Expr) => Expr): Boolean = {
        val old = funDef.postcondition
        val (res, postcondition) = {
          val (res, post) = old.getOrElse(FreshIdentifier("res").setType(funDef.returnType) -> BooleanLiteral(true))
          val args = funDef.params.map(_.toVariable)
          val sizePost = cmp(Tuple(funDef.params.map(_.toVariable)), res.toVariable)
          (res, And(post, sizePost))
        }

        funDef.postcondition = Some(res -> postcondition)

        val prec = matchToIfThenElse(funDef.precondition.getOrElse(BooleanLiteral(true)))
        val body = matchToIfThenElse(funDef.body.get)
        val post = matchToIfThenElse(postcondition)
        val formula = Implies(prec, Let(res, body, post))

        if (!solver.definitiveALL(formula)) {
          funDef.postcondition = old
          false
        } else {
          true
        }
      }

      // test if size is smaller or equal to input
      val weekConstraintHolds = strengthen(self.softDecreasing)

      if (weekConstraintHolds) {
        // try to improve postcondition with strictly smaller
        strengthen(self.sizeDecreasing)
      }

      strengthenedPost += funDef
    }
  }

  sealed abstract class SizeConstraint
  case object StrongDecreasing extends SizeConstraint
  case object WeakDecreasing extends SizeConstraint
  case object NoConstraint extends SizeConstraint

  /*
  private val strengthenedApp : MutableSet[FunDef] = MutableSet.empty

  protected def strengthened(fd: FunDef): Boolean = strengthenedApp(fd)

  private val appConstraint   : MutableMap[(FunDef, Identifier), SizeConstraint] = MutableMap.empty

  def applicationConstraint(fd: FunDef, id: Identifier, arg: Expr, args: Seq[Expr]): Expr = arg match {
    case AnonymousFunction(fargs, body) => appConstraint.get(fd -> id) match {
      case Some(StrongDecreasing) => self.sizeDecreasing(Tuple(args), Tuple(fargs.map(_.toVariable)))
      case Some(WeakDecreasing) => self.softDecreasing(Tuple(args), Tuple(fargs.map(_.toVariable)))
      case _ => BooleanLiteral(true)
    }
    case _ => BooleanLiteral(true)
  }

  def strengthenApplications(funDefs: Set[FunDef])(implicit solver: Processor with Solvable) {
    val transitiveFunDefs = funDefs ++ funDefs.flatMap(fd => self.program.callGraph.transitiveCallees(fd))
    val sortedFunDefs = transitiveFunDefs.toSeq.sortWith((fd1, fd2) => self.program.callGraph.transitivelyCalls(fd2, fd1))

    for (funDef <- sortedFunDefs if !strengthenedApp(funDef) && funDef.hasBody && self.terminates(funDef).isGuaranteed) {

      val appCollector = new CollectorWithPaths[(Identifier,Expr,Expr)] {
        def collect(e: Expr, path: Seq[Expr]): Option[(Identifier, Expr, Expr)] = e match {
          case FunctionApplication(Variable(id), args) => Some((id, And(path), Tuple(args)))
          case _ => None
        }
      }

      val applications = appCollector.traverse(funDef).distinct

      val funDefArgTuple = Tuple(funDef.args.map(_.toVariable))

      val allFormulas = for ((id, path, appArgs) <- applications) yield {
        val soft = Implies(path, self.softDecreasing(funDefArgTuple, appArgs))
        val hard = Implies(path, self.sizeDecreasing(funDefArgTuple, appArgs))
        id -> ((soft, hard))
      }

      val formulaMap = allFormulas.groupBy(_._1).mapValues(_.map(_._2).unzip)

      val constraints = for ((id, (weakFormulas, strongFormulas)) <- formulaMap) yield id -> {
        if (solver.definitiveALL(And(weakFormulas.toSeq), funDef.precondition)) {
          if (solver.definitiveALL(And(strongFormulas.toSeq), funDef.precondition)) {
            StrongDecreasing
          } else {
            WeakDecreasing
          }
        } else {
          NoConstraint
        }
      }

      val funDefHOArgs = funDef.args.map(_.id).filter(_.getType.isInstanceOf[FunctionType]).toSet

      val fiCollector = new CollectorWithPaths[(Expr, Expr, Seq[(Identifier,(FunDef, Identifier))])] {
        def collect(e: Expr, path: Seq[Expr]): Option[(Expr, Expr, Seq[(Identifier,(FunDef, Identifier))])] = e match {
          case FunctionInvocation(fd, args) if (funDefHOArgs intersect args.collect({ case Variable(id) => id }).toSet).nonEmpty =>
            Some((And(path), Tuple(args), (args zip fd.args).collect {
              case (Variable(id), vd) if funDefHOArgs(id) => id -> ((fd, vd.id))
            }))
          case _ => None
        }
      }

      val invocations = fiCollector.traverse(funDef)
      val id2invocations : Seq[(Identifier, ((FunDef, Identifier), Expr, Expr))] =
        invocations.flatMap(p => p._3.map(c => c._1 -> ((c._2, p._1, p._2))))
      val invocationMap  : Map[Identifier, Seq[((FunDef, Identifier), Expr, Expr)]] = 
        id2invocations.groupBy(_._1).mapValues(_.map(_._2))

      def constraint(id: Identifier, passings: Seq[((FunDef, Identifier), Expr, Expr)]): SizeConstraint = {
        if (constraints.get(id) == Some(NoConstraint)) NoConstraint
        else if (passings.exists(p => appConstraint.get(p._1) == Some(NoConstraint))) NoConstraint
        else passings.foldLeft[SizeConstraint](constraints.getOrElse(id, StrongDecreasing)) {
          case (constraint, (key, path, args)) =>

            lazy val strongFormula = Implies(path, self.sizeDecreasing(funDefArgTuple, args))
            lazy val weakFormula = Implies(path, self.softDecreasing(funDefArgTuple, args))

            (constraint, appConstraint.get(key)) match {
              case (_, Some(NoConstraint)) => scala.sys.error("Whaaaat!?!? This shouldn't happen...")
              case (_, None) => NoConstraint
              case (NoConstraint, _) => NoConstraint
              case (StrongDecreasing | WeakDecreasing, Some(StrongDecreasing)) =>
                if (solver.definitiveALL(weakFormula, funDef.precondition)) StrongDecreasing
                else NoConstraint
              case (StrongDecreasing, Some(WeakDecreasing)) =>
                if (solver.definitiveALL(strongFormula, funDef.precondition)) StrongDecreasing
                else if (solver.definitiveALL(weakFormula, funDef.precondition)) WeakDecreasing
                else NoConstraint
              case (WeakDecreasing, Some(WeakDecreasing)) =>
                if (solver.definitiveALL(weakFormula, funDef.precondition)) WeakDecreasing
                else NoConstraint
            }
        }
      }

      val outers = invocationMap.mapValues(_.filter(_._1._1 != funDef))
      funDefHOArgs.foreach { id => appConstraint(funDef -> id) = constraint(id, outers.getOrElse(id, Seq.empty)) }

      val selfs = invocationMap.mapValues(_.filter(_._1._1 == funDef))
      funDefHOArgs.foreach { id => appConstraint(funDef -> id) = constraint(id, selfs.getOrElse(id, Seq.empty)) }

      strengthenedApp += funDef
    }
  }
  */
}


// vim: set ts=4 sw=4 et:
