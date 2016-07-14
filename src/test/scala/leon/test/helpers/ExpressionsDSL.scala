/* Copyright 2009-2016 EPFL, Lausanne */

package leon.test.helpers

import org.scalatest.Assertions

import leon.purescala.Definitions._
import leon.purescala.Common._
import leon.purescala.Types._
import leon.purescala.Expressions._

import scala.language.implicitConversions

trait ExpressionsDSLVariables {
  val F = BooleanLiteral(false)
  val T = BooleanLiteral(true)

  def bi(x: Int)    = InfiniteIntegerLiteral(x)
  def b(x: Boolean) = BooleanLiteral(x)
  def i(x: Int)     = IntLiteral(x)
  def r(n: BigInt, d: BigInt)  = FractionalLiteral(n, d)

  val a = FreshIdentifier("a", Int32Type).toVariable
  val b = FreshIdentifier("b", Int32Type).toVariable
  val c = FreshIdentifier("c", Int32Type).toVariable

  val x = FreshIdentifier("x", IntegerType).toVariable
  val y = FreshIdentifier("y", IntegerType).toVariable
  val z = FreshIdentifier("z", IntegerType).toVariable

  val m = FreshIdentifier("m", RealType).toVariable
  val n = FreshIdentifier("n", RealType).toVariable
  val o = FreshIdentifier("o", RealType).toVariable

  val p = FreshIdentifier("p", BooleanType).toVariable
  val q = FreshIdentifier("q", BooleanType).toVariable
  val r = FreshIdentifier("r", BooleanType).toVariable
}

trait ExpressionsDSLProgram {
self: Assertions =>


  def id(name: String, tpe: TypeTree)(implicit pgm: Program): Identifier = {
    FreshIdentifier(name, tpe)
  }

  def id(name: String, tpeName: String, tps: Seq[TypeTree] = Nil)(implicit pgm: Program): Identifier = {
    id(name, classType(tpeName, tps))
  }

  def funDef(name: String)(implicit pgm: Program): FunDef = {
    pgm.lookupAll(name).collect {
      case fd: FunDef => fd
    }.headOption.getOrElse {
      fail(s"Failed to lookup function '$name' in program")
    }
  }

  def classDef(name: String)(implicit pgm: Program): ClassDef = {
    pgm.lookupAll(name).collect {
      case cd: ClassDef => cd
    }.headOption.getOrElse {
      fail(s"Failed to lookup class '$name' in program")
    }
  }

  def classType(name: String, tps: Seq[TypeTree] = Nil)(implicit pgm: Program): ClassType = {
    classDef(name) match {
      case acd: AbstractClassDef => AbstractClassType(acd, tps)
      case ccd: CaseClassDef => CaseClassType(ccd, tps)
    }
  }

  def caseClassDef(name: String)(implicit pgm: Program): CaseClassDef = {
    pgm.lookupAll(name).collect {
      case ccd: CaseClassDef => ccd
    }.headOption.getOrElse {
      fail(s"Failed to lookup case class '$name' in program")
    }
  }

  def moduleDef(name: String)(implicit pgm: Program): ModuleDef = {
    pgm.lookupAll(name).collect {
      case m: ModuleDef => m
    }.headOption.getOrElse {
      fail(s"Failed to lookup module '$name' in program")
    }
  }

  def cc(name: String)(args: Expr*)(implicit pgm: Program): Expr = {
    val cct = caseClassDef(name).typed(Seq())
    CaseClass(cct, args.toSeq)
  }

  def fcall(name: String)(args: Expr*)(implicit pgm: Program): Expr = {
    val tfd = funDef(name).typed(Seq())
    FunctionInvocation(tfd, args.toSeq)
  }
}

trait ExpressionsDSL extends ExpressionsDSLVariables with ExpressionsDSLProgram {
  self: Assertions =>
 
 
  implicit def int2IntLit(i: Int): IntLiteral = IntLiteral(i)
  implicit def bigInt2IntegerLit(i: BigInt): InfiniteIntegerLiteral = InfiniteIntegerLiteral(i)

}
