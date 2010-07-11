package orderedsets

import TreeOperations._

import purescala._
import Trees._
import Common._
import TypeTrees._
import Definitions._

object getAlpha {
  var program: Program = null

  def setProgram(p: Program) = program = p

  def isAlpha(varMap: Variable => Expr)(t: Expr): Option[Expr] = t match {
    case FunctionInvocation(fd, Seq(v@Variable(_))) => asCatamorphism(program, fd) match {
      case None => None
      case Some(lstMatch) => varMap(v) match {
        case CaseClass(cd, args) => {
          val (_, _, ids, rhs) = lstMatch.find(_._1 == cd).get
          val repMap = Map(ids.map(id => Variable(id): Expr).zip(args): _*)
          Some(searchAndReplace(repMap.get)(rhs))
        }
        case u@Variable(_) => {
          val c = Variable(FreshIdentifier("Coll", true)).setType(t.getType)
          // TODO: Keep track of these variables for M1(t, c)
          Some(c)
        }
        case _ => error("Bad substitution")
      }
      case _ => None
    }
    case _ => None
  }

  def apply(t: Expr, varMap: Variable => Expr): Expr = {
    searchAndReplace(isAlpha(varMap))(t)
  }

  //  def solve(e : Expr): Option[Boolean] = {
  //    searchAndReplace(isAlpha(x => x))(e)
  //    None
  //  }
}


