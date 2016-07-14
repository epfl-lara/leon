/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package solvers
package unrolling

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait TemplateEncoder[T] {
  def encodeId(id: Identifier): T
  def encodeExpr(bindings: Map[Identifier, T])(e: Expr): T
  def substitute(map: Map[T, T]): T => T

  // Encodings needed for unrollingbank
  def mkNot(v: T): T
  def mkOr(ts: T*): T
  def mkAnd(ts: T*): T
  def mkEquals(l: T, r: T): T
  def mkImplies(l: T, r: T): T

  def extractNot(v: T): Option[T]
}

