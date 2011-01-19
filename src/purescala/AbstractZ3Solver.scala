package purescala

import z3.scala._
import Common._
import Definitions._
import Extensions._
import Trees._
import TypeTrees._

// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait AbstractZ3Solver {
  val reporter : Reporter

  protected[purescala] var exprToZ3Id : Map[Expr,Z3AST]
  protected[purescala] def fromZ3Formula(tree : Z3AST) : Expr

  protected[purescala] def softFromZ3Formula(tree : Z3AST) : Option[Expr] = {
    try {
      Some(fromZ3Formula(tree))
    } catch {
      case _ => None
    }
  }
}
