package leon

import z3.scala._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import Extensions._

import scala.collection.mutable.{Map => MutableMap}
import scala.collection.mutable.{Set => MutableSet}

// This is just to factor out the things that are common in "classes that deal
// with a Z3 instance"
trait AbstractZ3Solver {
  self: Solver =>

  val reporter: Reporter

  class CantTranslateException(t: Z3AST) extends Exception("Can't translate from Z3 tree: " + t)

  protected[leon] var z3 : Z3Context
  protected[leon] var program : Program

  def typeToSort(tt: TypeTree): Z3Sort
  protected[leon] var adtTesters: Map[CaseClassDef, Z3FuncDecl]
  protected[leon] var adtConstructors: Map[CaseClassDef, Z3FuncDecl]
  protected[leon] var adtFieldSelectors: Map[Identifier, Z3FuncDecl]

  protected[leon] val mapRangeSorts: MutableMap[TypeTree, Z3Sort]
  protected[leon] val mapRangeSomeConstructors: MutableMap[TypeTree, Z3FuncDecl]
  protected[leon] val mapRangeNoneConstructors: MutableMap[TypeTree, Z3FuncDecl]
  protected[leon] val mapRangeSomeTesters: MutableMap[TypeTree, Z3FuncDecl]
  protected[leon] val mapRangeNoneTesters: MutableMap[TypeTree, Z3FuncDecl]
  protected[leon] val mapRangeValueSelectors: MutableMap[TypeTree, Z3FuncDecl]

  protected[leon] var funSorts: Map[TypeTree, Z3Sort]
  protected[leon] var funDomainConstructors: Map[TypeTree, Z3FuncDecl]
  protected[leon] var funDomainSelectors: Map[TypeTree, Seq[Z3FuncDecl]]

  protected[leon] var exprToZ3Id : Map[Expr,Z3AST]
  protected[leon] def fromZ3Formula(model: Z3Model, tree : Z3AST, expectedType: Option[TypeTree]) : Expr

  protected[leon] def softFromZ3Formula(model: Z3Model, tree : Z3AST, expectedType: TypeTree) : Option[Expr] = {
    try {
      Some(fromZ3Formula(model, tree, Some(expectedType)))
    } catch {
      case e: CantTranslateException => None
    }
  }

  protected[leon] def solveWithBounds(vc: Expr, forValidity: Boolean) : (Option[Boolean], Map[Identifier, Expr]) 

  protected[leon] def boundValues : Unit = {
    val lowerBound: Z3AST = z3.mkInt(Settings.testBounds._1, z3.mkIntSort)
    val upperBound: Z3AST = z3.mkInt(Settings.testBounds._2, z3.mkIntSort)

    def isUnbounded(field: VarDecl) : Boolean = field.getType match {
      case Int32Type => true
      case _ => false
    }

    def boundConstraint(boundVar: Z3AST) : Z3AST = {
      z3.mkAnd(z3.mkLE(lowerBound, boundVar), z3.mkLE(boundVar, upperBound))
    }

    // for all recursive type roots
    //   for all child ccd of a root
    //     if ccd contains unbounded types
    //       create bound vars (mkBound) for each field
    //       create pattern that says (valueBounds(ccd(f1, ..)))
    //       create axiom tree that says "values of unbounded types are within bounds"
    //       assert axiom for the tree above

    val roots = program.classHierarchyRoots
    for (root <- roots) {
      val children: List[CaseClassDef] = (root match {
        case c: CaseClassDef => List(c)
        case a: AbstractClassDef => a.knownChildren.filter(_.isInstanceOf[CaseClassDef]).map(_.asInstanceOf[CaseClassDef]).toList
      })
      for (child <- children) child match {
        case CaseClassDef(id, parent, fields) =>
          val unboundedFields = fields.filter(isUnbounded(_))
          if (!unboundedFields.isEmpty) {
            val boundVars = fields.zipWithIndex.map{case (f, i) => z3.mkBound(i, typeToSort(f.getType))}
            val term = adtConstructors(child)(boundVars : _*)
            val pattern = z3.mkPattern(term)
            //val constraint = (fields zip boundVars).filter((p: (VarDecl, Z3AST)) => isUnbounded(p._1)).map((p: (VarDecl, Z3AST)) => boundConstraint(p._2)).foldLeft(z3.mkTrue)((a, b) => a && b)
            val constraint = (fields zip boundVars).filter((p: (VarDecl, Z3AST)) => isUnbounded(p._1)).map((p: (VarDecl, Z3AST)) => boundConstraint(adtFieldSelectors(p._1.id)(term))).foldLeft(z3.mkTrue)((a, b) => z3.mkAnd(a, b))
            val axiom = z3.mkForAll(0, List(pattern), fields.zipWithIndex.map{case (f, i) => (z3.mkIntSymbol(i), typeToSort(f.getType))}, constraint)
            //println("Asserting: " + axiom)
            z3.assertCnstr(axiom)
          }
      }
    }
  }
}
