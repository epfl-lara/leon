package funcheck

import scala.tools.nsc._
import scala.tools.nsc.plugins._

trait CodeExtraction {
  self: AnalysisComponent =>

  import global._
  import StructuralExtractors._

  def findContracts(tree: Tree): Unit = tree match {
    case DefDef(/*mods*/ _, name, /*tparams*/ _, /*vparamss*/ _, /*tpt*/ _, body) => {
      var realBody = body
      var reqCont: Option[Tree] = None
      var ensCont: Option[Function] = None

      body match {
        case EnsuredExpression(body2, contract) => realBody = body2; ensCont = Some(contract)
        case _ => ;
      }

      realBody match {
        case RequiredExpression(body3, contract) => realBody = body3; reqCont = Some(contract)
        case _ => ;
      }

      println("In: " + name) 
      println("  Requires clause: " + reqCont)
      println("  Ensures  clause: " + ensCont)
      println("  Body:            " + realBody)
    }

    case _ => ;
  }

  def showObjects(tree: Tree): Unit = tree match {
    case ObjectDefn(name) => println(name + " appears to be an object.")
    case _ => ;
  }
}
