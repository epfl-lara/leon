package leon
package synthesis

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

object Heuristics {
  def all = Set[Synthesizer => Rule](
    new OptimisticGround(_),
    //new IntInduction(_),
    new CEGISOnSteroids(_),
    new OptimisticInjection(_)
  )
}

trait Heuristic {
  this: Rule =>

  override def toString = "H: "+name
}

class OptimisticGround(synth: Synthesizer) extends Rule("Optimistic Ground", synth, 90) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    if (!p.as.isEmpty && !p.xs.isEmpty) {
      val xss = p.xs.toSet
      val ass = p.as.toSet

      val tpe = TupleType(p.xs.map(_.getType))

      var i = 0;
      var maxTries = 3;

      var result: Option[RuleResult]   = None
      var predicates: Seq[Expr]        = Seq()

      while (result.isEmpty && i < maxTries) {
        val phi = And(p.phi +: predicates)
        synth.solver.solveSAT(phi) match {
          case (Some(true), satModel) =>
            val satXsModel = satModel.filterKeys(xss) 

            val newPhi = valuateWithModelIn(phi, xss, satModel)

            synth.solver.solveSAT(Not(newPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

              case (Some(false), _) =>
                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

              case _ =>
                result = Some(RuleInapplicable)
            }

          case (Some(false), _) =>
            if (predicates.isEmpty) {
              result = Some(RuleSuccess(Solution(BooleanLiteral(false), Error(p.phi+" is UNSAT!").setType(tpe))))
            } else {
              result = Some(RuleInapplicable)
            }
          case _ =>
            result = Some(RuleInapplicable)
        }

        i += 1 
      }

      result.getOrElse(RuleInapplicable)
    } else {
      RuleInapplicable
    }
  }
}


class IntInduction(synth: Synthesizer) extends Rule("Int Induction", synth, 80) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.as match {
      case List(origId) if origId.getType == Int32Type =>
        val tpe = TupleType(p.xs.map(_.getType))

        val inductOn = FreshIdentifier(origId.name, true).setType(origId.getType)

        val postXs  = p.xs map (id => FreshIdentifier("r", true).setType(id.getType))

        val postXsMap = (p.xs zip postXs).toMap.mapValues(Variable(_))

        val newPhi     = subst(origId -> Variable(inductOn), p.phi)
        val postCondGT = substAll(postXsMap + (origId -> Minus(Variable(inductOn), IntLiteral(1))), p.phi)
        val postCondLT = substAll(postXsMap + (origId -> Plus(Variable(inductOn), IntLiteral(1))), p.phi)

        val subBase = Problem(List(), p.c, subst(origId -> IntLiteral(0), p.phi), p.xs)
        val subGT   = Problem(inductOn :: postXs, p.c, And(Seq(newPhi, GreaterThan(Variable(inductOn), IntLiteral(0)), postCondGT)), p.xs)
        val subLT   = Problem(inductOn :: postXs, p.c, And(Seq(newPhi, LessThan(Variable(inductOn), IntLiteral(0)), postCondLT)), p.xs)

        val onSuccess: List[Solution] => Solution = {
          case List(base, gt, lt) =>
            val newFun = new FunDef(FreshIdentifier("rec", true), tpe, Seq(VarDecl(inductOn, inductOn.getType)))
            newFun.body = Some( 
              IfExpr(Equals(Variable(inductOn), IntLiteral(0)),
                base.toExpr,
              IfExpr(GreaterThan(Variable(inductOn), IntLiteral(0)),
                LetTuple(postXs, FunctionInvocation(newFun, Seq(Minus(Variable(inductOn), IntLiteral(1)))), gt.toExpr)
              , LetTuple(postXs, FunctionInvocation(newFun, Seq(Plus(Variable(inductOn), IntLiteral(1)))), lt.toExpr)))
            )

            Solution(BooleanLiteral(true), LetDef(newFun, FunctionInvocation(newFun, Seq(Variable(origId)))))
          case _ =>
            Solution.none
        }

        RuleStep(List(subBase, subGT, subLT), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

class OptimisticInjection(synth: Synthesizer) extends Rule("Opt. Injection", synth, 50) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (!candidates.isEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = And(newExprs))

      RuleStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class SelectiveInlining(synth: Synthesizer) extends Rule("Sel. Inlining", synth, 20) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val eqfuncalls = exprs.collect{
      case eq @ Equals(FunctionInvocation(fd, args), e) =>
        ((fd, e), args, eq : Expr)
      case eq @ Equals(e, FunctionInvocation(fd, args)) =>
        ((fd, e), args, eq : Expr)
    }

    val candidates = eqfuncalls.groupBy(_._1).filter(_._2.size > 1)
    if (!candidates.isEmpty) {

      var newExprs = exprs
      for (cands <- candidates.values) {
        val cand = cands.take(2)
        val toRemove = cand.map(_._3).toSet
        val argss    = cand.map(_._2)
        val args     = argss(0) zip argss(1)

        newExprs ++= args.map{ case (l, r) => Equals(l, r) }
        newExprs = newExprs.filterNot(toRemove)
      }

      val sub = p.copy(phi = And(newExprs))

      RuleStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class CEGISOnSteroids(synth: Synthesizer) extends Rule("cegis w. gen.", synth, 50) with Heuristic {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    case class Generator(tpe: TypeTree, altBuilder: () => List[(Expr, Set[Identifier])]);

    var generators = Map[TypeTree, Generator]()
    def getGenerator(t: TypeTree): Generator = generators.get(t) match {
      case Some(g) => g
      case None =>
        val alternatives: () => List[(Expr, Set[Identifier])] = t match {
          case BooleanType =>
            { () => List((BooleanLiteral(true), Set()), (BooleanLiteral(false), Set())) }

          case Int32Type =>
            { () => List((IntLiteral(0), Set()), (IntLiteral(1), Set())) }

          case TupleType(tps) =>
            { () =>
              val ids = tps.map(t => FreshIdentifier("t", true).setType(t))
              List((Tuple(ids.map(Variable(_))), ids.toSet))
            }

          case CaseClassType(cd) =>
            { () =>
              val ids = cd.fieldsIds.map(i => FreshIdentifier("c", true).setType(i.getType))
              List((CaseClass(cd, ids.map(Variable(_))), ids.toSet))
            }

          case AbstractClassType(cd) =>
            { () =>
              val alts: Seq[(Expr, Set[Identifier])] = cd.knownDescendents.flatMap(i => i match {
                  case acd: AbstractClassDef =>
                    synth.reporter.error("Unnexpected abstract class in descendants!")
                    None
                  case cd: CaseClassDef =>
                    val ids = cd.fieldsIds.map(i => FreshIdentifier("c", true).setType(i.getType))
                    Some((CaseClass(cd, ids.map(Variable(_))), ids.toSet))
              })
              alts.toList
            }

          case _ =>
            synth.reporter.error("Can't construct generator. Unsupported type: "+t+"["+t.getClass+"]");
            { () => Nil }
        }
        val g = Generator(t, alternatives)
        generators += t -> g
        g
    }

    case class TentativeFormula(f: Expr, recTerms: Map[Identifier, Set[Identifier]]) {
      def unroll: TentativeFormula = {
        var newF = this.f
        var newRecTerms = Map[Identifier, Set[Identifier]]()
        for ((_, recIds) <- recTerms; recId <- recIds) {
          val gen  = getGenerator(recId.getType)
          val alts = gen.altBuilder().map(alt => FreshIdentifier("b", true) -> alt)

          val pre = Or(alts.map{ case (id, _) => Variable(id) }) // b1 OR b2
          val cases = for((bid, (ex, rec)) <- alts.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            if (!rec.isEmpty) {
              newRecTerms += bid -> rec
            }
            Implies(Variable(bid), Equals(Variable(recId), ex))
          }

          newF = And(newF, And(pre :: cases))
        }

        TentativeFormula(newF, newRecTerms)
      }

      def closedFormula = And(f :: recTerms.keySet.map(id => Not(Variable(id))).toList)
    }

    var result: Option[RuleResult]   = None

    var ass = p.as.toSet

    var lastF     = TentativeFormula(p.phi, Map() ++ p.xs.map(x => x -> Set(x)))
    var currentF  = lastF.unroll
    var unrolings = 0
    do {
      println("Was: "+lastF.closedFormula)
      println("Now Trying : "+currentF.closedFormula)

      val tpe = TupleType(p.xs.map(_.getType))

      var i = 0;
      var maxTries = 10;

      var predicates: Seq[Expr]        = Seq()

      while (result.isEmpty && i < maxTries) {
        val phi = And(currentF.closedFormula +: predicates)
        synth.solver.solveSAT(phi) match {
          case (Some(true), satModel) =>
            val notAss = satModel.keySet.filterNot(ass)
            val satXsModel = satModel.filterKeys(notAss)

            val newPhi = valuateWithModelIn(phi, notAss, satModel)

            synth.solver.solveSAT(Not(newPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                predicates = valuateWithModelIn(phi, ass, invalidModel) +: predicates

              case (Some(false), _) =>
                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

              case _ =>
            }

          case (Some(false), _) =>
          case _ =>
        }

        i += 1 
      }

      lastF = currentF
      currentF = lastF.unroll
      unrolings += 1
    } while(unrolings < 5 && lastF != currentF && result.isEmpty)

    result.getOrElse(RuleInapplicable)
  }
}
