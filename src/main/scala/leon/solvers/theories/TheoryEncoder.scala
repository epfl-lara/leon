/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait TheoryEncoder { self =>
  protected val encoder: Encoder
  protected val decoder: Decoder

  private val idMap = new Bijection[Identifier, Identifier]
  private val fdMap = new Bijection[FunDef    , FunDef    ]
  private val cdMap = new Bijection[ClassDef  , ClassDef  ]

  def encode(id: Identifier): Identifier = encoder.transform(id)
  def decode(id: Identifier): Identifier = decoder.transform(id)

  def encode(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = encoder.transform(expr)
  def decode(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = decoder.transform(expr)

  def encode(tpe: TypeTree): TypeTree = encoder.transform(tpe)
  def decode(tpe: TypeTree): TypeTree = decoder.transform(tpe)

  def encode(fd: FunDef): FunDef = encoder.transform(fd)
  def decode(fd: FunDef): FunDef = decoder.transform(fd)

  protected class Encoder extends purescala.DefinitionTransformer(idMap, fdMap, cdMap)
  protected class Decoder extends purescala.DefinitionTransformer(idMap.swap, fdMap.swap, cdMap.swap)

  def >>(that: TheoryEncoder): TheoryEncoder = new TheoryEncoder {
    val encoder = new Encoder {
      override def transformExpr(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Option[Expr] = {
        val mapSeq = bindings.toSeq
        val intermediate = mapSeq.map { case (id, _) => id.duplicate(tpe = self.encoder.transform(id.getType)) }
        val e2 = self.encoder.transform(expr)((mapSeq zip intermediate).map { case ((id, _), id2) => id -> id2 }.toMap)
        Some(that.encoder.transform(e2)((intermediate zip mapSeq).map { case (id, (_, id2)) => id -> id2 }.toMap))
      }

      override def transformType(tpe: TypeTree): Option[TypeTree] = Some(that.encoder.transform(self.encoder.transform(tpe)))

      override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = {
        val (pat2, bindings) = self.encoder.transform(pat)
        val (pat3, bindings2) = that.encoder.transform(pat2)
        (pat3, bindings2.map { case (id, id2) => id -> bindings2(id2) })
      }
    }

    val decoder = new Decoder {
      override def transformExpr(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Option[Expr] = {
        val mapSeq = bindings.toSeq
        val intermediate = mapSeq.map { case (id, _) => id.duplicate(tpe = self.decoder.transform(id.getType)) }
        val e2 = that.decoder.transform(expr)((mapSeq zip intermediate).map { case ((id, _), id2) => id -> id2 }.toMap)
        Some(self.decoder.transform(e2)((intermediate zip mapSeq).map { case (id, (_, id2)) => id -> id2 }.toMap))
      }

      override def transformType(tpe: TypeTree): Option[TypeTree] = Some(self.decoder.transform(that.decoder.transform(tpe)))

      override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = {
        val (pat2, bindings) = that.decoder.transform(pat)
        val (pat3, bindings2) = self.decoder.transform(pat2)
        (pat3, bindings.map { case (id, id2) => id -> bindings2(id2) })
      }
    }
  }
}

class NoEncoder extends TheoryEncoder {
  val encoder = new Encoder
  val decoder = new Decoder
}

