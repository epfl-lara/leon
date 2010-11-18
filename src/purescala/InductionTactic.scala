package purescala

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._

class InductionTactic(reporter: Reporter) extends DefaultTactic(reporter) {
  override val description = "Induction tactic for suitable functions"
  override val shortDescription = "induction"

  private def singleAbsClassDef(args: VarDecls) : Option[AbstractClassDef] = {
    val filtered = args.filter(arg =>
      arg.getType match {
        case AbstractClassType(_) => true
        case _ => false
      })
    if (filtered.size != 1) None else (filtered.head.getType match {
      case AbstractClassType(classDef) => Some(classDef)
      case _ => scala.Predef.error("This should not happen.")
    })
  } 

  private def firstAbsClassDef(args: VarDecls) : Option[(AbstractClassDef, VarDecl)] = {
    val filtered = args.filter(arg =>
      arg.getType match {
        case AbstractClassType(_) => true
        case _ => false
      })
    if (filtered.size == 0) None else (filtered.head.getType match {
      case AbstractClassType(classDef) => Some((classDef, filtered.head))
      case _ => scala.Predef.error("This should not happen.")
    })
  } 

  private def selectorsOfParentType(parentType: ClassType, ccd: CaseClassDef, expr: Expr) : Seq[Expr] = {
    val childrenOfSameType = ccd.fields.filter(field => field.getType == parentType)
    for (field <- childrenOfSameType) yield {
      CaseClassSelector(ccd, expr, field.id).setType(parentType)
    }
  }

  override def generatePostconditions(funDef: FunDef) : Seq[VerificationCondition] = {
    assert(funDef.body.isDefined)
    val defaultPost = super.generatePostconditions(funDef)
    firstAbsClassDef(funDef.args) match {
      case Some((classDef, arg)) =>
        val prec = funDef.precondition
        val post = funDef.postcondition
        val body = matchToIfThenElse(funDef.body.get)
        val argAsVar = arg.toVariable

        if (post.isEmpty) {
          Seq.empty
        } else {
          val children = classDef.knownChildren
          val conditionsForEachChild = (for (child <- classDef.knownChildren) yield (child match {
            case ccd @ CaseClassDef(id, prnt, vds) =>
              val selectors = selectorsOfParentType(classDefToClassType(classDef), ccd, argAsVar)
              // if no subtrees of parent type, assert property for base case
              val resFresh = FreshIdentifier("result", true).setType(body.getType)
              val bodyAndPostForArg = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), matchToIfThenElse(post.get)))
              val withPrec = if (prec.isEmpty) bodyAndPostForArg else Implies(matchToIfThenElse(prec.get), bodyAndPostForArg)

              val conditionForChild = 
                if (selectors.size == 0) 
                  withPrec
                else {
                  val inductiveHypothesis = (for (sel <- selectors) yield {
                    val resFresh = FreshIdentifier("result", true).setType(body.getType)
                    val bodyAndPost = Let(resFresh, replace(Map(argAsVar -> sel), body), replace(Map(ResultVariable() -> Variable(resFresh), argAsVar -> sel), matchToIfThenElse(post.get))) 
                    val withPrec = if (prec.isEmpty) bodyAndPost else Implies(replace(Map(argAsVar -> sel), matchToIfThenElse(prec.get)), bodyAndPost)
                    withPrec
                  })
                  Implies(And(inductiveHypothesis), withPrec)
                }
              new VerificationCondition(Implies(CaseClassInstanceOf(ccd, argAsVar), conditionForChild), funDef, VCKind.Postcondition, this)
            case _ => error("Abstract class has non-case class subtype.")
          }))
          println("Induction tactic yields the following VCs:")
          println(conditionsForEachChild.map(vc => vc.condition).mkString("\n"))
          conditionsForEachChild
        }
      case None =>
        reporter.warning("Induction tactic currently supports exactly one argument of abstract class type")
        defaultPost
    }
  }
}
