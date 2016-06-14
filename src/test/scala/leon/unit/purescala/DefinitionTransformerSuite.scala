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
  private val classAField = FreshIdentifier("x", IntegerType)
  classA.setFields(Seq(ValDef(classAField)))
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


  test("transforming function invocation update FunDef used in the call only") {
    val originalFd = fd1
    val tr1 = new DefinitionTransformer {
      override def transformType(t: TypeTree): Option[TypeTree] = t match {
        case IntegerType => Some(BooleanType)
        case _ => None
      }
    }

    val fi = FunctionInvocation(originalFd.typed, Seq(IntLiteral(3)))
    val nfi = tr1.transform(fi)(Map())
    nfi match {
      case FunctionInvocation(nfd, Seq(arg)) => {
        assert(nfd.fd !== originalFd)
        assert(nfd.fd.params.size === 1)
        assert(nfd.fd.params(0).getType === BooleanType) 
        assert(originalFd.params.size === 1)
        assert(originalFd.params(0).getType === IntegerType)
      }
      case _ => assert(false)
    }
    
    //yes, that is because we didn't specify a mapping for IntLiteral to Booleans. 
    //The system is expected to not crash, and still perform the transformation.
    //In practice, one could then perform additional transformation using other means in
    //order to fix the program
    assert(nfi.getType === Untyped)
  }

  private val instanceA = FreshIdentifier("a", classA.typed)
  private val fd4 = new FunDef(FreshIdentifier("f4"), Seq(), Seq(ValDef(instanceA)), IntegerType)
  fd4.body = Some(bi(42))
  private val fd5 = new FunDef(FreshIdentifier("f5"), Seq(), Seq(ValDef(x.id)), IntegerType)
  fd5.body = Some(FunctionInvocation(fd4.typed, Seq(CaseClass(classA.typed, Seq()))))

  test("transforming function invocation update FunDef and transitive defs") {
    val tr1 = new DefinitionTransformer {
      override def transformType(t: TypeTree): Option[TypeTree] = t match {
        case IntegerType => Some(BooleanType)
        case _ => None
      }
    }

    val fi = FunctionInvocation(fd5.typed, Seq(IntLiteral(3)))
    val nfi = tr1.transform(fi)(Map())
    nfi match {
      case FunctionInvocation(nfd, Seq(arg)) => {
        assert(nfd.fd !== fd5)
        assert(nfd.fd.params.size === 1)
        assert(nfd.fd.params(0).getType === BooleanType) 

        assert(nfd.body.nonEmpty)
        nfd.fd.body.foreach(bd => bd match {
          case FunctionInvocation(nfd2, Seq(_)) => {
            assert(nfd2.fd !== fd4)
            assert(nfd2.fd.params.size === 1)
            nfd2.fd.params(0).getType match {
              case CaseClassType(ccd, Seq()) =>
                assert(ccd !== classA)
                assert(ccd.fields.size === 1)
                assert(ccd.fields(0).getType === BooleanType)
              case _ => assert(false)
            }
          }
        })
      }
      case _ => assert(false)
    }
  }

  test("transforming class to adt with invariants containing selectors") {
    val dummyClass = new CaseClassDef(FreshIdentifier("Dummy"), Seq(), None, false)
    val dummyClassTransformer = new CaseClassDef(FreshIdentifier("DummyTransformer"), Seq(), None, false)

    val classWithSimpleField = new CaseClassDef(FreshIdentifier("A"), Seq(), None, false)
    val simpleField = FreshIdentifier("t", dummyClass.typed)
    classWithSimpleField.setFields(Seq(ValDef(simpleField)))

    val invariantThis = FreshIdentifier("this", classWithSimpleField.typed)
    val simpleInvariant = new FunDef(FreshIdentifier("inv"), Seq(), Seq(ValDef(invariantThis)), BooleanType)
    simpleInvariant.body = Some(LessEquals(CaseClassSelector(classWithSimpleField.typed, invariantThis.toVariable, simpleField) , bi(0)))
    classWithSimpleField.setInvariant(simpleInvariant)

    val classDefTransformer = new DefinitionTransformer {
      override def transformClassDef(cd: ClassDef): Option[ClassDef] = cd match {
        case t if t == dummyClass => Some(dummyClassTransformer)
        case _ => None
      }
    }

    val simpleId = FreshIdentifier("id", classWithSimpleField.typed)
    val transformedId = classDefTransformer.transform(simpleId)
    assert(simpleId !== transformedId)
    assert(simpleId.getType === classWithSimpleField.typed)
    val transformedIdClassDef: ClassDef = transformedId.getType.asInstanceOf[ClassType].classDef
    assert(transformedIdClassDef.fields.size === 1)
    assert(transformedIdClassDef.fields(0).getType === dummyClassTransformer.typed)


    val typeTransformer = new DefinitionTransformer {
      override def transformType(t: TypeTree): Option[TypeTree] = t match {
        case t if t == dummyClass.typed => Some(dummyClassTransformer.typed)
        case _ => None
      }
    }

    val transformedId2 = typeTransformer.transform(simpleId)
    assert(simpleId !== transformedId)
    assert(simpleId.getType === classWithSimpleField.typed)
    val transformedId2ClassDef: ClassDef = transformedId.getType.asInstanceOf[ClassType].classDef
    assert(transformedId2ClassDef.fields.size === 1)
    assert(transformedId2ClassDef.fields(0).getType === dummyClassTransformer.typed)
  }


  test("transformClassDef is only called once on each class in program") {
    //this checks that transformClassDef is only applied once on a class in
    //the program. The freshClass only record the first fresh class returned,
    //and in the end we check that the transformation on the classA is equals
    //to the fresh class. We try to run the transformation on a fundef with
    //many references to class A to have a non-trivial testcase
    var freshClass: Option[ClassDef] = None
    val transformer = new DefinitionTransformer {
      override def transformClassDef(cd: ClassDef): Option[ClassDef] = cd match {
        case t if t == classA =>
          val freshA = classA.duplicate(fields = classA.fields.map(vd => ValDef(vd.id.freshen))) 
          if(freshClass.isEmpty) freshClass = Some(freshA)
          Some(freshA)
        case _ => None
      }
    }

   
    val a = FreshIdentifier("a", classA.typed)
    val fd = new FunDef(FreshIdentifier("f"), Seq(), Seq(ValDef(a)), classA.typed)
    fd.body = Some(CaseClassSelector(classA.typed, a.toVariable, classAField))

    transformer.transform(fd)
    assert(transformer.transform(classA) == freshClass.getOrElse(null))
  }

}
