/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.xlang

import org.scalatest._

import leon.test._
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Types._
import leon.purescala.TypeOps.isSubtypeOf
import leon.purescala.Definitions._
import leon.xlang.Expressions._
import leon.xlang.ExprOps._
import leon.xlang.Constructors._

class ExprOpsSuite extends FunSuite with helpers.ExpressionsDSL {

  test("flattenBlocks does not change a simple block") {
    assert(flattenBlocks(Block(Seq(y), x)) === Block(Seq(y), x))
    assert(flattenBlocks(Block(Seq(y, z), x)) === Block(Seq(y, z), x))
  }

  test("flattenBlocks of a single statement removes the block") {
    assert(flattenBlocks(Block(Seq(), x)) === x)
    assert(flattenBlocks(Block(Seq(), y)) === y)
  }

  test("flattenBlocks of a one nested block flatten everything") {
    assert(flattenBlocks(Block(Seq(Block(Seq(y), z)), x)) === Block(Seq(y, z), x))
    assert(flattenBlocks(Block(Seq(y, Block(Seq(), z)), x)) === Block(Seq(y, z), x))
  }

  test("flattenBlocks of a several nested blocks flatten everything") {
    assert(flattenBlocks(Block(Seq(Block(Seq(), y), Block(Seq(), z)), x)) === Block(Seq(y, z), x))
  }

  test("flattenBlocks of a nested block in last expr should flatten") {
    assert(flattenBlocks(Block(Seq(Block(Seq(), y)), Block(Seq(z), x))) === Block(Seq(y, z), x))
  }

  test("flattenBlocks should eliminate intermediate UnitLiteral") {
    assert(flattenBlocks(Block(Seq(UnitLiteral(), y, z), x)) === Block(Seq(y, z), x))
    assert(flattenBlocks(Block(Seq(y, UnitLiteral(), z), x)) === Block(Seq(y, z), x))
    assert(flattenBlocks(Block(Seq(UnitLiteral(), UnitLiteral(), z), x)) === Block(Seq(z), x))
    assert(flattenBlocks(Block(Seq(UnitLiteral()), x)) === x)
  }

  test("flattenBlocks should not eliminate trailing UnitLiteral") {
    assert(flattenBlocks(Block(Seq(x), UnitLiteral())) === Block(Seq(x), UnitLiteral()))
  }

  test("block Constructor should simplify an empty list to unit") {
    assert(block(Seq()) === UnitLiteral())
  }

  test("block Constructor should create a normal block for a simple block") {
    assert(block(Seq(y, z)) === Block(Seq(y), z))
  }

  test("block Constructor should eliminate a unit in a simple block") {
    assert(block(Seq(y, UnitLiteral(), z)) === Block(Seq(y), z))
  }

  test("block Constructor should transform a single element list to that elemetn") {
    assert(block(Seq(y)) === y)
  }

  test("block Constructor should filter units from a single element list and return a non-block") {
    assert(block(Seq(UnitLiteral(), y)) === y)
  }

  test("block Constructor should transform a list of units to unit") {
    assert(block(Seq(UnitLiteral(), UnitLiteral())) === UnitLiteral())
  }

}
