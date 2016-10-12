/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Common._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import scala.reflect.ClassTag

private[converters] trait GenericConverter {
  this: Converters with MiniReporter =>

  // Apply the conversion function and make sure the resulting AST matches our expectation
  def convertTo[T](tree: Tree)(implicit funCtx: FunCtx, ct: ClassTag[T]): T = convert(tree) match {
    case t: T => t
    case x    => internalError(s"Expected an instance of $ct when converting $tree but got $x")
  }

  // Generic conversion functions
  // Currently simple aliases in case we need later to have special treatment instead
  def convertToType  (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Type](tree)
  def convertToStruct(tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Struct](tree)
  def convertToStmt  (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Stmt](tree)
  def convertToVar   (tree: Tree)(implicit funCtx: FunCtx) = convertTo[CAST.Var](tree)

  // No need of FunCtx for identifiers
  def convertToId(tree: Tree) = {
    implicit val ctx = FunCtx.empty
    convertTo[CAST.Id](tree)
  }

  // This is the main conversion function, defined in Converters
  def convert(tree: Tree)(implicit funCtx: FunCtx): CAST.Tree

}

