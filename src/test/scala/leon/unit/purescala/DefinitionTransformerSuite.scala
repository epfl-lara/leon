/* Copyright 2009-2016 EPFL, Lausanne */

package leon.unit.purescala

import org.scalatest._

import leon.test.helpers.ExpressionsDSL
import leon.purescala.Common._
import leon.purescala.Expressions._
import leon.purescala.Extractors._
import leon.purescala.DefinitionTransformer
import leon.purescala.Definitions._
import leon.purescala.Types._

class DefinitionTransformerSuite extends FunSuite with ExpressionsDSL {

  private val fd1 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd1.body = Some(x)

  private val fd2 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd2.body = Some(Plus(x, bi(1)))

  private val fd3 = new FunDef(FreshIdentifier("f1"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd3.body = Some(Times(x, bi(1)))

  test("transformation with no rewriting should not change FunDef") {
    val tr1 = new DefinitionTransformer
    assert(tr1.transform(fd1) === fd1)
    assert(tr1.transform(fd2) === fd2)
    assert(tr1.transform(fd3) === fd3)
  }

}
