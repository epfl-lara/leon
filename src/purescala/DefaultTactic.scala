package purescala

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import Extensions.Tactic

class DefaultTactic(reporter: Reporter) extends Tactic(reporter) {
    val description = "Default verification condition generation approach"
    override val shortDescription = "default"

    var _prog : Option[Program] = None
    def program : Program = _prog match {
      case None => throw new Exception("Program never set in DefaultTactic.")
      case Some(p) => p
    }

    override def setProgram(program: Program) : Unit = {
      _prog = Some(program)
    }

    def generatePostconditions(functionDefinition: FunDef) : Seq[VerificationCondition] = {
      assert(functionDefinition.body.isDefined)
      val prec = functionDefinition.precondition
      val post = functionDefinition.postcondition
      val body = functionDefinition.body.get

      if(post.isEmpty) {
        Seq.empty
      } else {
        val theExpr = { 
          val resFresh = FreshIdentifier("result", true).setType(body.getType)
          val bodyAndPost = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), post.get))
          val withPrec = if(prec.isEmpty) {
            bodyAndPost
          } else {
            Implies(prec.get, bodyAndPost)
          }

          import Analysis._
        
          if(Settings.experimental) {
            reporter.info("Raw:")
            reporter.info(withPrec)
            reporter.info("Raw, expanded:")
            reporter.info(expandLets(withPrec))
          }
          reporter.info(" - inlining...")
          val expr0 = inlineNonRecursiveFunctions(program, withPrec)
          if(Settings.experimental) {
            reporter.info("Inlined:")
            reporter.info(expr0)
            reporter.info("Inlined, expanded:")
            reporter.info(expandLets(expr0))
          }
          reporter.info(" - unrolling...")
          val expr1 = unrollRecursiveFunctions(program, expr0, Settings.unrollingLevel)
          if(Settings.experimental) {
            reporter.info("Unrolled:")
            reporter.info(expr1)
            reporter.info("Unrolled, expanded:")
            reporter.info(expandLets(expr1))
          }
          reporter.info(" - inlining contracts...")
          val expr2 = inlineContracts(expr1)
          if(Settings.experimental) {
            reporter.info("Contract'ed:")
            reporter.info(expr2)
            reporter.info("Contract'ed, expanded:")
            reporter.info(expandLets(expr2))
          }
          reporter.info(" - converting pattern-matching...")
          val expr3 = if(Settings.useNewPatternMatchingTranslator) {
            matchToIfThenElse(expr2)
          } else {
            rewriteSimplePatternMatching(expr2)
          }
          if(Settings.experimental) {
            reporter.info("Pattern'ed:")
            reporter.info(expr3)
            reporter.info("Pattern'ed, expanded:")
            reporter.info(expandLets(expr3))
          }
          expr3
        }
        Seq(new VerificationCondition(theExpr, functionDefinition, VCKind.Postcondition, this))
      }
    }

    def generatePreconditions(function: FunDef) : Seq[VerificationCondition] = {
      Seq.empty
    }

    def generatePatternMatchingExhaustivenessChecks(function: FunDef) : Seq[VerificationCondition] = {
      Seq.empty
    }

    def generateMiscCorrectnessConditions(function: FunDef) : Seq[VerificationCondition] = {
      Seq.empty
    }
}
