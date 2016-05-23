package leon
package invariant.util

import purescala.Common._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import invariant.factories._
import solvers._
import TemplateIdFactory._

/**
 * An abstract class for mapping integer typed variables to reals and vice-versa.
 * Note: this preserves the template identifier property
 */
abstract class IntRealMap {
  var oldToNew = Map[Identifier, Identifier]()
  var newToOld = Map[Identifier, Identifier]()

  def mapLiteral(l: Literal[_]): Literal[_]
  def unmapLiteral(l: Literal[_]): Literal[_]
  def mapIdentifier(v: Identifier): Identifier

  def mapExpr(inexpr: Expr): Expr = {
    val transformer = (e: Expr) => e match {
      case l : Literal[_] => mapLiteral(l)
      case v@Variable(id) =>
        Variable(oldToNew.getOrElse(id, {
          val mid = mapIdentifier(id)
          if (mid != id) {
            oldToNew += (id -> mid)
            newToOld += (mid -> id)
          }
          mid
        }))
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }

  def unmapModel(model: Model): Model = {
    new Model(model.map {
      case (key, value) if (newToOld.contains(key)) =>
        (newToOld(key),
          value match {
            case l: Literal[_] => unmapLiteral(l)
            case e             => e
          })
      case other => other
    }.toMap)
  }

  def mapModel(model: Model): Model = {
    new Model(model.map {
      case (k, v) if (oldToNew.contains(k)) =>
        (oldToNew(k), v match {
            case l: Literal[_] => mapLiteral(l)
            case e             => e
          })
      case other => other
    }.toMap)
  }
}

/**
 * maps all real valued variables and literals to new integer variables/literals and
 * performs the reverse mapping
 */
class RealToInt extends IntRealMap {

  val bone = BigInt(1)
  def mapLiteral(l: Literal[_]): Literal[_] = l match {
     case FractionalLiteral(num, `bone`) => InfiniteIntegerLiteral(num)
     case FractionalLiteral(_, _) => throw new IllegalStateException("Real literal with non-unit denominator")
     case other => other
  }

  def unmapLiteral(l: Literal[_]): Literal[_] = l match {
    case InfiniteIntegerLiteral(v) => FractionalLiteral(v.toInt, 1)
    case other => other
  }

  def mapIdentifier(v: Identifier): Identifier =
    if (v.getType == RealType) {
      if (IsTemplateIdentifier(v)) freshIdentifier(v.name)
      else FreshIdentifier(v.name, IntegerType, true)
    } else v
}

/**
 * Maps integer literal and identifiers to real literal and identifiers
 */
/*class IntToReal extends IntRealMap {

  def mapLiteral(l: Literal[_]): Literal[_] = l match {
    case InfiniteIntegerLiteral(v) => FractionalLiteral(v.toInt, 1)
    case other => other
  }

  *//**
   * Here, we return fractional literals for integer-valued variables,
   * and leave to the client to handle them
   *//*
  def unmapLiteral(l: Literal[_]): Literal[_] = l

  def mapIdentifier(v: Identifier): Identifier =
    if (v.getType == IntegerType) {
      if (IsTemplateIdentifier(v)) freshIdentifier(v.name, RealType)
      else FreshIdentifier(v.name, RealType, true)
    } else v
}*/