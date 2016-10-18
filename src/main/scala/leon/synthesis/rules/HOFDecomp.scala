/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules

import leon.utils.SeqUtils._
import solvers._

import purescala.Path
import purescala.Expressions._
import purescala.Common._
import purescala.Definitions._
import purescala.Types._
import purescala.TypeOps._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Constructors._

case object HOFDecomp extends Rule("HOFDecomp") {
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    // Look for HOFs to call that are only missing a HOF argument
    val fd      = hctx.functionContext
    val program = hctx.program
    val tpe     = tupleTypeWrap(p.xs.map(_.getType))

    val recursives = program.callGraph.transitiveCallers(hctx.functionContext) + fd

    val solverf = SolverFactory.getFromSettings(hctx, program).withTimeout(1000L)

    def toExclude(fd: FunDef) = {
      fd.isSynthetic ||
      fd.isInner ||
      !fd.body.exists(isDeterministic) ||
      recursives(fd)
    }

    def isHOFParam(vd: ValDef): Boolean = vd.getType.isInstanceOf[FunctionType]

    def isHOF(fd: FunDef): Boolean = fd.params.exists(isHOFParam)

    def getCandidates(fd: FunDef): Seq[RuleInstantiation] = {
      val free = fd.tparams.map(_.tp)

      instantiation_<:(fd.returnType, tpe) match {
        case Some(tpsMap1) =>
          /* Finding compatible calls:
           * Example candidate:
           *   map[T, Int](List[T], (T => Int): List[Int]    where T is still free
           *
           * We now need to infer T based on ''as''
           */

          val tfd = fd.typed(free.map(tp => tpsMap1.getOrElse(tp, tp)))

          val hofParams = tfd.params.filter(isHOFParam)

          // Only one HO-parameter allowed, for now
          if (hofParams.size != 1) {
            return Nil
          }

          val hofId = FreshIdentifier("F", hofParams.head.getType, true)

          /* Given a function 'map(l: List[T], f: T => B): List[B]' found in
           * scope, we extract the HO-parameter f, and make sure 'normal'
           * arguments l, are either directly mapped to an existing input, or
           * to a free variable.
           *
           * We first instantiate type params according to return value.
           */

          var freeVariables = Set[Identifier]()

          val altsPerArgs = tfd.params.zipWithIndex.map { case (vd, i) =>
            if (isHOFParam(vd)) {
              // Only one possibility for the HOF argument
              Seq(hofId)
            } else {
              // For normal arguments, we either map to a free variable (and
              // then ask solver for a model), or to an input

              val optFree = if (i > 0) {
                // Hack: First argument is the most important, we should not
                // obtain its value from a model. We don't want:
                // Nil.fold(..)

                Some(FreshIdentifier("v", vd.getType, true))
              } else {
                None
              }

              freeVariables ++= optFree

              // Note that this is an over-approximation, since
              // Int <: T and
              // Bool <: T can both be true in two distinct calls to
              // canBeSubtypeOf with T free
              //
              // We refine later.
              val compatibleInputs = {
                p.as.filter(a => instantiation_>:(vd.getType, a.getType).nonEmpty)
              }

              compatibleInputs ++ optFree
            }
          }

          //println("-"*80)
          //println("Considering function: "+tfd.asString)

          val asSet = p.as.toSet

          val calls = cartesianProduct(altsPerArgs).flatMap { vs =>
            /*
             * We want at least one input to be used.
             */
            if (vs.exists(v => asSet(v))) {
              /*
               * We then instantiate remaining type params based on available
               * arguments.
               */
              val argsTpe   = tupleTypeWrap(vs.map(_.getType))
              val paramsTpe = tupleTypeWrap(tfd.params.map(_.getType))

              //println(s"${paramsTpe.asString} >: ${argsTpe.asString} (${stillFree.map(_.asString).mkString(", ")})")

              // Check that all arguments are compatible, together.
              val paramsTpeInst = instantiateType(paramsTpe, tpsMap1)
              instantiation_<:(paramsTpeInst, argsTpe) match {
                case Some(tpsMap2) =>
                  val tpsMap = tpsMap1 ++ tpsMap2
                  val tfd = fd.typed(free.map(tp => tpsMap.getOrElse(tp, tp)))

                  val hofId2 = instantiateType(hofId, tpsMap)

                  val vs2 = vs.map { v => subst(hofId -> hofId2.toVariable, v.toVariable) }

                  Some((FunctionInvocation(tfd, vs2), hofId2))
                case _ =>
                  None
              }
            } else {
              None
            }
          }

          val results = for ((c, hofId) <- calls) yield {
            println("-"*80)
            println("Considering call: "+c.asString)

            /* All variables that are used for the call are considered as
             * captured, they are not closed over within the closure.
             *
             * The rationale is that if the variable is used for the HOF call,
             * it is likely not needed within the closure as well. For example:
             *
             *   list.foldLeft(x, { (a: Int, b: Int) =>  ...do not close over x or list... })
             */

            val captured = variablesOf(c)
            val free = captured & freeVariables
            val env = p.as.filterNot(captured)

            /* Instead of using our hofId directly, like:
             *  F: A => B
             * we use a function Fgen(env): A => B
             */

            val fgen = FreshIdentifier("Fgen", FunctionType(env.map(_.getType), hofId.getType))

            val fgenCall = Application(fgen.toVariable, env.map(_.toVariable))

            val paramC = subst(hofId -> fgenCall, c)

            /* Build constraints to detect if  HOF call is compatible with
             * tests. Env specializes the calls.
             *
             * We check if there exists a model for Fgen(env) that satisfies
             * all tests. This translates to checking if a model exists for F
             * given a specific env.
             */

            val cnstrs = p.eb.valids.collect {
              case InOutExample(ins, outs) =>
                equality(substAll(p.as.zip(ins).toMap, paramC), tupleWrap(outs))
            }

            val cnstr = andJoin(cnstrs)

            //println("Constraint: "+cnstr.asString)

            val solver = solverf.getNewSolver()
            try {
              solver.assertCnstr(cnstr)
              solver.check match {
                case Some(true) =>
                  val model = solver.getModel
                  //println("Model: "+model.asString)

                  val freeValuations = free.flatMap { id =>
                    model.get(id).map { m => id -> m }
                  }.toMap

                  /* We extract valuations from ''fgen'' which gives us a model
                   * for F per env. */
                  val tests = model.get(fgen) match {
                    case Some(FiniteLambda(envToF, _, _)) =>
                      envToF.flatMap {
                        case (envValuation, FiniteLambda(values, _, _)) =>
                          values.flatMap {
                            case (ins, out) =>
                              //println("Test:")
                              //println(s"$ins  --->  $out")

                              /* Given a model with Fgen(env*)(X) -> Y,
                               * we check if we can use ''(env*, X) -> Y'' as
                               * in/out test for the closure. This is done by
                               * making sure we don't over-commit with this
                               * test (Y really is the only acceptable output)
                               */

                              val solver2 = solverf.getNewSolver()
                              solver2.assertCnstr(substAll(freeValuations, cnstr))
                              val f = Application(fgen.toVariable, envValuation)
                              solver2.assertCnstr(not(equality(Application(f, ins), out)))

                              val isUnique = solver2.check.contains(false)
                              //println("IsUnique? "+isUnique)
                              //if (!isUnique) {
                              //  println("Alternative: "+solver2.getModel.asString)
                              //}
                              solverf.reclaim(solver2)

                              if (isUnique) {
                                Some(InOutExample(envValuation ++ ins, Seq(out)))
                              } else {
                                None
                              }
                          }
                        }
                    case res =>
                      //println("Model of "+fgen+": "+res)
                      Nil
                  }

                  val eb = ExamplesBank(tests, Nil)
                  println(eb.asString("Tests:"))

                  // Heuristic: we don't want to synthesize HOFs with only one tests, those are trivial and ininteresting
                  if (tests.size > 1) {
                    val cAssigned = substAll(freeValuations, c)

                    val (ls, xs) = hofId.getType match {
                      case FunctionType(froms, to) =>
                        (froms.toList.map(tpe => FreshIdentifier("a", tpe, true)), List(FreshIdentifier("x", to, true)))
                    }

                    val as = env ++ ls

                    // TODO: collect pc that concerns ''env''
                    val subs = List(
                      Problem(as, BooleanLiteral(true), Path.empty, BooleanLiteral(true), xs, eb)
                    )

                    val onSuccess: List[Solution] => Option[Solution] = {
                      case List(sol) =>

                        if (sol.pre == BooleanLiteral(true)) {
                          val term = subst(hofId -> Lambda(ls.map(ValDef), sol.term), cAssigned)

                          Some(Solution(BooleanLiteral(true), sol.defs, term, sol.isTrusted))
                        } else {
                          None
                        }
                      case _ =>
                        None
                    }

                    val desc = {
                      val hole = FreshIdentifier("_", hofId.getType).toVariable
                      "Call HOF function "+subst(hofId -> hole, cAssigned).asString
                    }

                    Some(decomp(subs, onSuccess, desc))
                  } else {
                    None
                  }
                case Some(false) =>
                  println("UNSAT")
                  None

                case None =>
                  println("UNKNOWN")
                  None
              }
            } finally {
              solverf.reclaim(solver)
            }
          }

          results.flatten

        case None =>
          Nil
      }
    }


    visibleFunDefsFromMain(program).filter(isHOF).filterNot(toExclude).toSeq.sortBy(_.id).flatMap(getCandidates)
  }
}
