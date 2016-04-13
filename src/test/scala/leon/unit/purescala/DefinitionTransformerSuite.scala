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

  private val fd2 = new FunDef(FreshIdentifier("f2"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd2.body = Some(Plus(x, bi(1)))

  private val fd3 = new FunDef(FreshIdentifier("f3"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd3.body = Some(Times(x, bi(1)))

  test("transformation with no rewriting should not change FunDef") {
    val tr1 = new DefinitionTransformer
    assert(tr1.transform(fd1) === fd1)
    assert(tr1.transform(fd2) === fd2)
    assert(tr1.transform(fd3) === fd3)
  }


  private val classA = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
  classA.setFields(Seq(ValDef(FreshIdentifier("x", IntegerType))))
  private val classB = new CaseClassDef(FreshIdentifier("B"), Seq(), None, false)
  classB.setFields(Seq(ValDef(FreshIdentifier("a", classA.typed))))

  test("transformating type of a nested case class change all related case classes") {
    val tr1 = new DefinitionTransformer {
      override def transformType(t: TypeTree): Option[TypeTree] = t match {
        case IntegerType => Some(BooleanType)
        case _ => None
      }
    }
    val classA2 = tr1.transform(classA)
    assert(classA.id !== classA2.id)
    assert(classA.fields.head.id !== classA2.fields.head.id)
    assert(classA.fields.head.getType === IntegerType)
    assert(classA2.fields.head.getType === BooleanType)
    assert(tr1.transform(classA) === classA2)

    val classB2 = tr1.transform(classB)
    assert(tr1.transform(classA) === classA2)
    assert(classB.id !== classB2.id)
    assert(classB.fields.head.id !== classB2.fields.head.id)
    assert(classB.fields.head.getType === classA.typed)
    assert(classB2.fields.head.getType === classA2.typed)

  }

}
