package leon
package synthesis

import purescala.Common._
import purescala.ScalaPrinter
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._
import LinearEquations.elimVariable
import ArithmeticNormalization.simplify

object Rules {
  def all = Set[Synthesizer => Rule](
    new Unification.DecompTrivialClash(_),
    new Unification.OccursCheck(_),
    new ADTDual(_),
    new OnePoint(_),
    new Ground(_),
    new CaseSplit(_),
    new UnusedInput(_),
    new UnconstrainedOutput(_),
    new OptimisticGround(_),
    new CEGIS(_),
    new Assert(_),
    new IntegerEquation(_)
  )
}

sealed abstract class RuleResult
case object RuleInapplicable extends RuleResult
case class RuleSuccess(solution: Solution) extends RuleResult
case class RuleMultiSteps(subProblems: List[Problem],
                          steps: List[List[Solution] => List[Problem]],
                          onSuccess: List[Solution] => (Solution, Boolean)) extends RuleResult

object RuleStep {
  def apply(subProblems: List[Problem], onSuccess: List[Solution] => Solution) = {
    RuleMultiSteps(subProblems, Nil, onSuccess.andThen((_, true)))
  }
}

abstract class Rule(val name: String, val synth: Synthesizer, val priority: Priority) {
  def applyOn(task: Task): RuleResult

  def subst(what: Tuple2[Identifier, Expr], in: Expr): Expr = replace(Map(Variable(what._1) -> what._2), in)
  def substAll(what: Map[Identifier, Expr], in: Expr): Expr = replace(what.map(w => Variable(w._1) -> w._2), in)

  val forward: List[Solution] => Solution = {
    case List(s) => Solution(s.pre, s.defs, s.term)
    case _ => Solution.none
  }

  override def toString = "R: "+name
}

class OnePoint(synth: Synthesizer) extends Rule("One-point", synth, 300) {
  def applyOn(task: Task): RuleResult = {

    val p = task.problem

    val TopLevelAnds(exprs) = p.phi

    val candidates = exprs.collect {
      case eq @ Equals(Variable(x), e) if (p.xs contains x) && !(variablesOf(e) contains x) =>
        (x, e, eq)
      case eq @ Equals(e, Variable(x)) if (p.xs contains x) && !(variablesOf(e) contains x) =>
        (x, e, eq)
    }

    if (!candidates.isEmpty) {
      val (x, e, eq) = candidates.head

      val others = exprs.filter(_ != eq)
      val oxs    = p.xs.filter(_ != x)

      val newProblem = Problem(p.as, p.c, subst(x -> e, And(others)), oxs)

      val onSuccess: List[Solution] => Solution = { 
        case List(Solution(pre, defs, term)) =>
          if (oxs.isEmpty) {
            Solution(pre, defs, Tuple(e :: Nil)) 
          } else {
            Solution(pre, defs, LetTuple(oxs, term, subst(x -> e, Tuple(p.xs.map(Variable(_)))))) 
          }
        case _ => Solution.none
      }

      RuleStep(List(newProblem), onSuccess)
    } else {
      RuleInapplicable
    }
  }
}

class Ground(synth: Synthesizer) extends Rule("Ground", synth, 500) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    if (p.as.isEmpty) {

      val tpe = TupleType(p.xs.map(_.getType))

      synth.solver.solveSAT(p.phi) match {
        case (Some(true), model) =>
          RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(model))).setType(tpe)))
        case (Some(false), model) =>
          RuleSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe)))
        case _ =>
          RuleInapplicable
      }
    } else {
      RuleInapplicable
    }
  }
}

class CaseSplit(synth: Synthesizer) extends Rule("Case-Split", synth, 200) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    p.phi match {
      case Or(Seq(o1, o2)) =>
        val sub1 = Problem(p.as, p.c, o1, p.xs)
        val sub2 = Problem(p.as, p.c, o2, p.xs)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(p1, d1, t1), Solution(p2, d2, t2)) => Solution(Or(p1, p2), d1++d2, IfExpr(p1, t1, t2))
          case _ => Solution.none
        }

        RuleStep(List(sub1, sub2), onSuccess)
      case _ =>
        RuleInapplicable
    }
  }
}

class Assert(synth: Synthesizer) extends Rule("Assert", synth, 200) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    p.phi match {
      case TopLevelAnds(exprs) =>
        val xsSet = p.xs.toSet

        val (exprsA, others) = exprs.partition(e => (variablesOf(e) & xsSet).isEmpty)

        if (!exprsA.isEmpty) {
          if (others.isEmpty) {
            RuleSuccess(Solution(And(exprsA), Set(), Tuple(p.xs.map(id => simplestValue(Variable(id))))))
          } else {
            val sub = p.copy(c = And(p.c +: exprsA), phi = And(others))

            RuleStep(List(sub), forward)
          }
        } else {
          RuleInapplicable
        }
      case _ =>
        RuleInapplicable
    }
  }
}

class UnusedInput(synth: Synthesizer) extends Rule("UnusedInput", synth, 100) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unused = p.as.toSet -- variablesOf(p.phi) -- variablesOf(p.c)

    if (!unused.isEmpty) {
      val sub = p.copy(as = p.as.filterNot(unused))

      RuleStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class UnconstrainedOutput(synth: Synthesizer) extends Rule("Unconstr.Output", synth, 100) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem
    val unconstr = p.xs.toSet -- variablesOf(p.phi)

    if (!unconstr.isEmpty) {
      val sub = p.copy(xs = p.xs.filterNot(unconstr))

      val onSuccess: List[Solution] => Solution = { 
        case List(s) =>
          Solution(s.pre, s.defs, LetTuple(sub.xs, s.term, Tuple(p.xs.map(id => if (unconstr(id)) simplestValue(Variable(id)) else Variable(id)))))
        case _ =>
          Solution.none
      }

      RuleStep(List(sub), onSuccess)
    } else {
      RuleInapplicable
    }

  }
}

object Unification {
  class DecompTrivialClash(synth: Synthesizer) extends Rule("Unif Dec./Clash/Triv.", synth, 200) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val (toRemove, toAdd) = exprs.collect {
        case eq @ Equals(cc1 @ CaseClass(cd1, args1), cc2 @ CaseClass(cd2, args2)) =>
          if (cc1 == cc2) {
            (eq, List(BooleanLiteral(true)))
          } else if (cd1 == cd2) {
            (eq, (args1 zip args2).map((Equals(_, _)).tupled))
          } else {
            (eq, List(BooleanLiteral(false)))
          }
      }.unzip

      if (!toRemove.isEmpty) {
        val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))


        RuleStep(List(sub), forward)
      } else {
        RuleInapplicable
      }
    }
  }

  class OccursCheck(synth: Synthesizer) extends Rule("Unif OccursCheck", synth, 200) {
    def applyOn(task: Task): RuleResult = {
      val p = task.problem

      val TopLevelAnds(exprs) = p.phi

      val isImpossible = exprs.exists {
        case eq @ Equals(cc : CaseClass, Variable(id)) if variablesOf(cc) contains id =>
          true
        case eq @ Equals(Variable(id), cc : CaseClass) if variablesOf(cc) contains id =>
          true
        case _ =>
          false
      }

      if (isImpossible) {
        val tpe = TupleType(p.xs.map(_.getType))

        RuleSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe)))
      } else {
        RuleInapplicable
      }
    }
  }
}


class ADTDual(synth: Synthesizer) extends Rule("ADTDual", synth, 200) {
  def applyOn(task: Task): RuleResult = {
    val p = task.problem

    val xs = p.xs.toSet
    val as = p.as.toSet

    val TopLevelAnds(exprs) = p.phi


    val (toRemove, toAdd) = exprs.collect {
      case eq @ Equals(cc @ CaseClass(cd, args), e) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) -- xs).isEmpty =>
        (eq, CaseClassInstanceOf(cd, e) +: (cd.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cd, e, id)) } )
      case eq @ Equals(e, cc @ CaseClass(cd, args)) if (variablesOf(e) -- as).isEmpty && (variablesOf(cc) -- xs).isEmpty =>
        (eq, CaseClassInstanceOf(cd, e) +: (cd.fieldsIds zip args).map{ case (id, ex) => Equals(ex, CaseClassSelector(cd, e, id)) } )
    }.unzip

    if (!toRemove.isEmpty) {
      val sub = p.copy(phi = And((exprs.toSet -- toRemove ++ toAdd.flatten).toSeq))

      RuleStep(List(sub), forward)
    } else {
      RuleInapplicable
    }
  }
}

class CEGIS(synth: Synthesizer) extends Rule("CEGIS", synth, 50) {
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

          val bvs = altsWithBranches.map(alt => Variable(alt._1))
          val distinct = if (bvs.size > 1) {
            (for (i <- (1 to bvs.size-1); j <- 0 to i-1) yield {
              Or(Not(bvs(i)), Not(bvs(j)))
            }).toList
          } else {
            List(BooleanLiteral(true))
          }
          val pre = And(Or(bvs) :: distinct) // (b1 OR b2) AND (Not(b1) OR Not(b2))
          val cases = for((bid, (ex, rec)) <- altsWithBranches.toList) yield { // b1 => E(gen1, gen2)     [b1 -> {gen1, gen2}]
            if (!rec.isEmpty) {
              newRecTerms += bid -> rec
            }
            newMappings += bid -> (recId -> ex)

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

    var lastF     = TentativeFormula(Implies(p.c, p.phi), BooleanLiteral(true), Map(), Map() ++ p.xs.map(x => x -> Set(x)))
    var currentF  = lastF.unroll
    var unrolings = 0
    val maxUnrolings = 2
    do {
      //println("Was: "+lastF.entireFormula)
      //println("Now Trying : "+currentF.entireFormula)

      val tpe = TupleType(p.xs.map(_.getType))
      val bss = currentF.bss

      var predicates: Seq[Expr]        = Seq()
      var continue = true

      while (result.isEmpty && continue) {
        val basePhi = currentF.entireFormula
        val constrainedPhi = And(basePhi +: predicates)
        //println("-"*80)
        //println("To satisfy: "+constrainedPhi)
        synth.solver.solveSAT(constrainedPhi) match {
          case (Some(true), satModel) =>
            //println("Found candidate!: "+satModel.filterKeys(bss))

            //println("Corresponding program: "+simplifyTautologies(synth.solver)(valuateWithModelIn(currentF.program, bss, satModel)))
            val fixedBss = And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)
            //println("Phi with fixed sat bss: "+fixedBss)

            val counterPhi = Implies(And(fixedBss, currentF.program), currentF.phi)
            //println("Formula to validate: "+counterPhi)

            synth.solver.solveSAT(Not(counterPhi)) match {
              case (Some(true), invalidModel) =>
                // Found as such as the xs break, refine predicates
                //println("Found counter EX: "+invalidModel)
                predicates = Not(And(bss.map(b => Equals(Variable(b), satModel(b))).toSeq)) +: predicates
                //println("Let's avoid this case: "+bss.map(b => Equals(Variable(b), satModel(b))).mkString(" "))

              case (Some(false), _) =>
                //println("Sat model: "+satModel.toSeq.sortBy(_._1.toString).map{ case (id, v) => id+" -> "+v }.mkString(", "))
                var mapping = currentF.mappings.filterKeys(satModel.mapValues(_ == BooleanLiteral(true))).values.toMap

                //println("Mapping: "+mapping)

                // Resolve mapping
                for ((c, e) <- mapping) {
                  mapping += c -> substAll(mapping, e)
                }

                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(mapping))).setType(tpe))))

              case _ =>
            }

          case (Some(false), _) =>
            //println("%%%% UNSAT")
            continue = false
          case _ =>
            //println("%%%% WOOPS")
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

class OptimisticGround(synth: Synthesizer) extends Rule("Optimistic Ground", synth, 90) {
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
                result = Some(RuleSuccess(Solution(BooleanLiteral(true), Set(), Tuple(p.xs.map(valuateWithModel(satModel))).setType(tpe))))

              case _ =>
                result = Some(RuleInapplicable)
            }

          case (Some(false), _) =>
            if (predicates.isEmpty) {
              result = Some(RuleSuccess(Solution(BooleanLiteral(false), Set(), Error(p.phi+" is UNSAT!").setType(tpe))))
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

class IntegerEquation(synth: Synthesizer) extends Rule("Integer Equation", synth, 300) {
  def applyOn(task: Task): RuleResult = {

    val p = task.problem

    val TopLevelAnds(exprs) = p.phi
    val xs = p.xs
    val as = p.as
    val formula = p.phi

    val (eqs, others) = exprs.partition(_.isInstanceOf[Equals])
    var candidates: Seq[Expr] = eqs
    var allOthers: Seq[Expr] = others

    var vars: Set[Identifier] = Set()
    var eqas: Set[Identifier] = Set()
    var eqxs: List[Identifier] = List()
    var ys: Set[Identifier] = Set()

    var optionNormalizedEq: Option[List[Expr]] = None
    while(!candidates.isEmpty && optionNormalizedEq == None) {
      val eq@Equals(_,_) = candidates.head
      candidates = candidates.tail
      
      vars = variablesOf(eq)
      eqas = as.toSet.intersect(vars)

      eqxs = xs.toSet.intersect(vars).toList
      ys = xs.toSet.diff(vars)

      try {
        optionNormalizedEq = Some(ArithmeticNormalization(Minus(eq.left, eq.right), eqxs.toArray).toList)
      } catch {
        case ArithmeticNormalization.NonLinearExpressionException(_) =>
      }
    }

    optionNormalizedEq match {
      case None => RuleInapplicable
      case Some(normalizedEq0) => {
        val (neqxs, normalizedEq) = eqxs.zip(normalizedEq0.tail).filterNot{ case (_, IntLiteral(0)) => true case _ => false}.unzip

        if(normalizedEq.size == 1) {


        } else {

        val (eqPre, eqWitness, eqFreshVars) = elimVariable(eqas, normalizedEq)

        val eqSubstMap: Map[Expr, Expr] = neqxs.zip(eqWitness).map{case (id, e) => (Variable(id), simplify(e))}.toMap
        val freshFormula = simplify(replace(eqSubstMap, And(allOthers)))
        }
        (eqPre, freshFormula)

        val newProblem = Problem(as, And(eqPre, p.c), freshFormula, eqFreshVars)

        val onSuccess: List[Solution] => Solution = { 
          case List(Solution(pre, defs, term)) =>
            if (eqFreshVars.isEmpty) {
              Solution(pre, defs, replace(eqSubstMap, Tuple(neqxs.map(Variable(_)))))
            } else {
              Solution(pre, defs, LetTuple(eqFreshVars, term, replace(eqSubstMap, Tuple(neqxs.map(Variable(_))))))
            }
          case _ => Solution.none
        }

        RuleStep(List(newProblem), onSuccess)
      }
    }

  }
}
