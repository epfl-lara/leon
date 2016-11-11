package leon
package xlang

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.DefOps._
import purescala.Types._
import purescala.Constructors._
import purescala.Extractors._
import purescala.DependencyFinder
import purescala.DefinitionTransformer
import utils.Bijection
import xlang.Expressions._
import xlang.ExprOps._

object EffectsChecking extends UnitPhase[Program] {

  val name = "effects-checking"
  val description = "Ensure certain Leon effect and alias restrictions"

  def apply(ctx: LeonContext, pgm: Program): Unit = {
    val effectsAnalysis = new EffectsAnalysis

    pgm.definedFunctions.foreach(fd => {

      fd.postcondition.foreach{ case post@Lambda(vds, body) => {
        val effects = effectsAnalysis(body)
        if(effects.nonEmpty) {
          ctx.reporter.fatalError(post.getPos, "Postcondition has effects on: " + effects.head)
        }
      }}

      fd.precondition.foreach(pre => {
        val effects = effectsAnalysis(pre)
        if(effects.nonEmpty) {
          ctx.reporter.fatalError(pre.getPos, "Precondition has effects on: " + effects.head)
        }
      })

      fd.body.foreach(body => {
        preTraversal{
          case Assert(pred, _, _) => {
            val effects = effectsAnalysis(pred)
            if(effects.nonEmpty) {
              ctx.reporter.fatalError(pred.getPos, "Assertion has effects on: " + effects.head)
            }
          }
          case wh@While(_, _) => {
            wh.invariant.foreach(invariant => {
              val effects = effectsAnalysis(invariant) 
              if(effects.nonEmpty) {
                ctx.reporter.fatalError(invariant.getPos, "Loop invariant has effects on: " + effects.head)
              }
            })
          }
          case m@MatchExpr(_, cses) => {
            cses.foreach(cse => {
              cse.optGuard.foreach(guard => {
                val effects = effectsAnalysis(guard)
                if(effects.nonEmpty) {
                  ctx.reporter.fatalError(guard.getPos, "Pattern guard has effects on: " + effects.head)
                }
              })

              PatternOps.preTraversal{
                case pat@UnapplyPattern(_, unapply, _) => {
                  val effects = effectsAnalysis(unapply.fd)
                  if(effects.nonEmpty) {
                    ctx.reporter.fatalError(pat.getPos, "Pattern unapply has effects on: " + effects.head)
                  }
                }
                case _ => ()
              }(cse.pattern)
              
            })
          }
          case _ => ()
        }(body)
      })

    })
  }
}

