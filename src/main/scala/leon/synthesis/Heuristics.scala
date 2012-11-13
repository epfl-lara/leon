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
    new CEGIS(_),
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

class CEGIS(synth: Synthesizer) extends Rule("CEGIS", synth, 50) with Heuristic {
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

    def inputAlternatives(t: TypeTree): List[(Expr, Set[Identifier])] = {
      p.as.filter(a => isSubtypeOf(a.getType, t)).map(id => (Variable(id) : Expr, Set[Identifier]()))
    }

    case class TentativeFormula(phi: Expr,
                                program: Expr,
                                mappings: Map[Identifier, (Identifier, Expr)],
                                recTerms: Map[Identifier, Set[Identifier]]) {
      def unroll: TentativeFormula = {
        var newProgram  = List[Expr]()
        var newRecTerms = Map[Identifier, Set[Identifier]]()
        var newMappings = Map[Identifier, (Identifier, Expr)]()

        for ((_, recIds) <- recTerms; recId <- recIds) {
          val gen  = getGenerator(recId.getType)
          val alts = gen.altBuilder() ::: inputAlternatives(recId.getType)

          val altsWithBranches = alts.map(alt => FreshIdentifier("b", true).setType(BooleanType) -> alt)

          val pre = Or(altsWithBranches.map{ case (id, _) => Variable(id) }) // b1 OR b2
          val cases = for((bid, (ex, rec)) <- altsWithBranches.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            if (!rec.isEmpty) {
              newRecTerms += bid -> rec
            } else {
              newMappings += bid -> (recId -> ex)
            }

            Implies(Variable(bid), Equals(Variable(recId), ex))
          }

          newProgram = newProgram ::: pre :: cases
        }

        TentativeFormula(phi, And(program :: newProgram), mappings ++ newMappings, newRecTerms)
      }

      def bounds = recTerms.keySet.map(id => Not(Variable(id))).toList
      def bss = mappings.keySet

      def entireFormula = And(phi :: program :: bounds)
    }

    var result: Option[RuleResult]   = None

    var ass = p.as.toSet
    var xss = p.xs.toSet

    var lastF     = TentativeFormula(And(p.c, p.phi), BooleanLiteral(true), Map(), Map() ++ p.xs.map(x => x -> Set(x)))
    var currentF  = lastF.unroll
    var unrolings = 0
    val maxUnrolings = 2
    do {
      println("Was: "+lastF.entireFormula)
      println("Now Trying : "+currentF.entireFormula)

      val tpe = TupleType(p.xs.map(_.getType))
      val bss = currentF.bss

      var predicates: Seq[Expr]        = Seq()
      var continue = true

      while (result.isEmpty && continue) {
        val basePhi = currentF.entireFormula
        val constrainedPhi = And(basePhi +: predicates)
        println("-"*80)
        println("To satisfy: "+constrainedPhi)
        synth.solver.solveSAT(constrainedPhi) match {
          case (Some(true), satModel) =>
            println("Found candidate!: "+satModel.filterKeys(bss))

            val fixedBss = And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)
            println("Phi with fixed sat bss: "+fixedBss)

            val counterPhi = Implies(And(fixedBss, currentF.program), currentF.phi)
            println("Formula to validate: "+counterPhi)

            synth.solver.solveSAT(Not(counterPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                println("Found counter EX: "+invalidModel)
                predicates = Not(And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)) +: predicates
                println("Let's avoid this case: "+bss.map(b => Equals(Variable(b), satModel(b))).mkString(" "))

              case (Some(false), _) =>
                val mapping = currentF.mappings.filterKeys(satModel.mapValues(_ == BooleanLiteral(true))).values.toMap
                println("Mapping: "+mapping)
                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Tuple(p.xs.map(valuateWithModel(mapping))).setType(tpe))))

              case _ =>
            }

          case (Some(false), _) =>
            continue = false
          case _ =>
            continue = false
        }
      }

      lastF = currentF
      currentF = currentF.unroll
      unrolings += 1
    } while(unrolings < maxUnrolings && lastF != currentF && result.isEmpty)

    result.getOrElse(RuleInapplicable)
  }
}
