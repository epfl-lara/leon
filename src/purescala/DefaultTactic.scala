package purescala

import purescala.Common._
import purescala.Trees._
import purescala.Definitions._
import Extensions.Tactic

import scala.collection.mutable.{Map => MutableMap}

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
      val body = matchToIfThenElse(functionDefinition.body.get)

      if(post.isEmpty) {
        Seq.empty
      } else {
        val theExpr = { 
          val resFresh = FreshIdentifier("result", true).setType(body.getType)
          val bodyAndPost = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), matchToIfThenElse(post.get)))
          val withPrec = if(prec.isEmpty) {
            bodyAndPost
          } else {
            Implies(matchToIfThenElse(prec.get), bodyAndPost)
          }

          import Analysis._

          if(Settings.zeroInlining) {
            withPrec
          } else {
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
            expr2
          }
        }
        Seq(new VerificationCondition(theExpr, functionDefinition, VCKind.Postcondition, this))
      }
    }
  
    private val errConds : MutableMap[FunDef,Seq[VerificationCondition]] = MutableMap.empty
    private def errorConditions(function: FunDef) : Seq[VerificationCondition] = {
      if(errConds.isDefinedAt(function)) {
        errConds(function)
      } else {
        val conds = if(function.hasBody) {
          val bodyToUse = if(function.hasPrecondition) {
            IfExpr(function.precondition.get, function.body.get, Error("XXX").setType(function.returnType)).setType(function.returnType)
          } else {
            function.body.get
          }
          val withExplicit = expandLets(explicitPreconditions(matchToIfThenElse(bodyToUse)))
  
          val allPathConds = collectWithPathCondition((_ match { case Error(_) => true ; case _ => false }), withExplicit)
  
          allPathConds.filter(_._2 != Error("XXX")).map(pc => pc._2 match {
            case Error("precondition violated") => new VerificationCondition(Not(And(pc._1)), function, VCKind.Precondition, this)
            case Error("non-exhaustive match") => new VerificationCondition(Not(And(pc._1)), function, VCKind.ExhaustiveMatch, this)
            case _ => scala.Predef.error("Don't know what to do with this path condition target: " + pc._2)
          }).toSeq
        } else {
          Seq.empty
        }
        errConds(function) = conds
        conds
      }
    }

    def generatePreconditions(function: FunDef) : Seq[VerificationCondition] = {
      val toRet = errorConditions(function).filter(_.kind == VCKind.Precondition)

      println("PRECONDITIONS FOR " + function.id.name)
      println(toRet.map(_.condition).toList.mkString("\n"))
      toRet
    }

    def generatePatternMatchingExhaustivenessChecks(function: FunDef) : Seq[VerificationCondition] = {
      errorConditions(function).filter(_.kind == VCKind.ExhaustiveMatch)
    }

    def generateMiscCorrectnessConditions(function: FunDef) : Seq[VerificationCondition] = {
      Seq.empty
    }

    // prec: there should be no lets and no pattern-matching in this expression
    private def collectWithPathCondition(matcher: Expr=>Boolean, expression: Expr) : Set[(Seq[Expr],Expr)] = {
      var collected : Set[(Seq[Expr],Expr)] = Set.empty

      def rec(expr: Expr, path: List[Expr]) : Unit = {
        if(matcher(expr)) {
          collected = collected + ((path.reverse, expr))
        }

        expr match {
          case IfExpr(cond, then, elze) => {
            rec(cond, path)
            rec(then, cond :: path)
            rec(elze, Not(cond) :: path)
          }
          case NAryOperator(args, _) => args.foreach(rec(_, path))
          case BinaryOperator(t1, t2, _) => rec(t1, path); rec(t2, path)
          case UnaryOperator(t, _) => rec(t, path)
          case t : Terminal => ;
          case _ => scala.Predef.error("Unhandled tree in collectWithPathCondition : " + expr)
        }
      }

      rec(expression, Nil)
      collected
    }
}
