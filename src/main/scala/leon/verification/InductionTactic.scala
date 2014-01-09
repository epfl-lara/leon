/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package verification

import purescala.Common._
import purescala.Trees._
import purescala.TreeOps._
import purescala.HOTreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

class InductionTactic(reporter: Reporter) extends DefaultTactic(reporter) {
  override val description = "Induction tactic for suitable functions"
  override val shortDescription = "induction"

  private def firstAbsClassType(args: VarDecls) : Option[(AbstractClassType, VarDecl)] = {
    val filtered = args.filter(arg =>
      arg.getType match {
        case AbstractClassType(_, _) => true
        case _ => false
      })
    if (filtered.size == 0) None else (filtered.head.getType match {
      case act @ AbstractClassType(_, _) => Some((act, filtered.head))
      case _ => scala.sys.error("This should not happen.")
    })
  }

  private def selectorsOfParentType(parentType: ClassType, cct: CaseClassType, expr: Expr) : Seq[Expr] = {
    val childrenOfSameType = cct.fields.filter(field => field.getType == parentType)
    for (field <- childrenOfSameType) yield {
      CaseClassSelector(cct, expr, field.id).setType(parentType)
    }
  }

  override def generatePostconditions(funDef: FunDef) : Seq[VerificationCondition] = {
    assert(funDef.body.isDefined)
    val defaultPost = super.generatePostconditions(funDef)
    firstAbsClassType(funDef.args) match {
      case Some((classType, arg)) =>
        val prec = funDef.precondition
        val optPost = funDef.postcondition
        val body = matchToIfThenElse(funDef.body.get)
        val argAsVar = arg.toVariable

        optPost match {
          case None =>
            Seq.empty
          case Some((pid, post)) =>
            val conditionsForEachChild = (for (child <- classType.knownChildren) yield (child match {
              case cct @ CaseClassType(ccd, _) =>
                val selectors = selectorsOfParentType(classType, cct, argAsVar)
                // if no subtrees of parent type, assert property for base case
                val resFresh = FreshIdentifier("result", true).setType(body.getType)
                val bodyAndPostForArg = Let(resFresh, body, replace(Map(Variable(pid) -> Variable(resFresh)), matchToIfThenElse(post)))
                val withPrec = if (prec.isEmpty) bodyAndPostForArg else {
                  Implies(killForallExpressions(matchToIfThenElse(prec.get)), bodyAndPostForArg)
                }

                val conditionForChild = 
                  if (selectors.size == 0) 
                    withPrec
                  else {
                    val inductiveHypothesis = (for (sel <- selectors) yield {
                      val resFresh = FreshIdentifier("result", true).setType(body.getType)
                      val bodyAndPost = Let(resFresh, replace(Map(argAsVar -> sel), body), replace(Map(Variable(pid) -> Variable(resFresh), argAsVar -> sel), matchToIfThenElse(post))) 
                      val withPrec = if (prec.isEmpty) bodyAndPost else {
                        Implies(replace(Map(argAsVar -> sel), killForallExpressions(matchToIfThenElse(prec.get))), bodyAndPost)
                      }
                      withPrec
                    })
                    Implies(And(inductiveHypothesis), withPrec)
                  }
                new VerificationCondition(Implies(CaseClassInstanceOf(cct, argAsVar), conditionForChild), funDef, VCKind.Postcondition, this)
              case _ => scala.sys.error("Abstract class has non-case class subtype.")
            }))
            conditionsForEachChild
        }

      case None =>
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        defaultPost
    }
  }

  override def generatePreconditions(function: FunDef) : Seq[VerificationCondition] = {
    val defaultPrec = super.generatePreconditions(function)
    firstAbsClassType(function.args) match {
      case Some((classType, arg)) => {
        val toRet = if(function.hasBody) {
          val cleanBody = expandLets(matchToIfThenElse(function.body.get))

          val allPathConds = collectWithPathCondition((t => t match {
            case FunctionInvocation(fd, _) if(fd.hasPrecondition) => true
            case _ => false
          }), cleanBody)

          def withPrec(path: Seq[Expr], shouldHold: Expr) : Expr = if(function.hasPrecondition) {
            Not(And(And(killForallExpressions(matchToIfThenElse(function.precondition.get)) +: path), Not(shouldHold)))
          } else {
            Not(And(And(path), Not(shouldHold)))
          }

          val conditionsForAllPaths : Seq[Seq[VerificationCondition]] = allPathConds.map(pc => {
            val path : Seq[Expr] = pc._1
            val fi = pc._2.asInstanceOf[FunctionInvocation]
            val FunctionInvocation(fd, args) = fi

            val conditionsForEachChild = (for (child <- classType.knownChildren) yield (child match {
              case cct @ CaseClassType(ccd, _) => {
                val argAsVar = arg.toVariable
                val selectors = selectorsOfParentType(classType, cct, argAsVar)
                
                val prec : Expr = freshenLocals(matchToIfThenElse(fd.precondition.get))
                val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
                val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
                val newBody : Expr = replace(substMap, prec)
                val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

                val toProve = withPrec(path, newCall)

                val conditionForChild =
                  if (selectors.isEmpty)
                    toProve
                  else {
                    val inductiveHypothesis = (for (sel <- selectors) yield {
                      val prec : Expr = freshenLocals(matchToIfThenElse(fd.precondition.get))
                      val newLetIDs = fd.args.map(a => FreshIdentifier("arg_" + a.id.name, true).setType(a.tpe))
                      val substMap = Map[Expr,Expr]((fd.args.map(_.toVariable) zip newLetIDs.map(Variable(_))) : _*)
                      val newBody : Expr = replace(substMap, prec)
                      val newCall : Expr = (newLetIDs zip args).foldRight(newBody)((iap, e) => Let(iap._1, iap._2, e))

                      val toReplace = withPrec(path, newCall)
                      replace(Map(argAsVar -> sel), toReplace)
                    })
                    Implies(And(inductiveHypothesis), toProve)
                  }
                new VerificationCondition(Implies(CaseClassInstanceOf(cct, argAsVar), conditionForChild), function, VCKind.Precondition, this).setPos(fi)
              }
              case _ => scala.sys.error("Abstract class has non-case class subtype")
            }))
            conditionsForEachChild
          }).toSeq

          conditionsForAllPaths.flatten
        } else {
          Seq.empty
        }
        toRet
      }
      case None => {
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        defaultPrec
      }
    }
  }
}
