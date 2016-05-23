/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package datagen

import purescala.Expressions._
import purescala.Types._
import purescala.Definitions._
import purescala.Common._
import purescala.Constructors._
import solvers._
import utils._

class SolverDataGen(ctx: LeonContext, pgm: Program, sf: SolverFactory[Solver]) extends DataGenerator {
  implicit val ctx0 = ctx

  def generate(tpe: TypeTree): FreeableIterator[Expr] = {
    generateFor(Seq(FreshIdentifier("tmp", tpe)), BooleanLiteral(true), 20, 20).map(_.head).takeWhile(_ => !interrupted.get)
  }

  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): FreeableIterator[Seq[Expr]] = {
    if (ins.isEmpty) {
      FreeableIterator.empty
    } else {

      var fds = Map[ClassDef, FunDef]()

      def sizeFor(of: Expr): Expr = of.getType match {
        case AbstractClassType(acd, tps) =>
          val fd = fds.getOrElse(acd, {
            val actDef = AbstractClassType(acd, acd.tparams.map(_.tp))

            val e = FreshIdentifier("e", actDef)

            val fd: FunDef = new FunDef(FreshIdentifier("sizeOf", Untyped), acd.tparams, Seq(ValDef(e)), IntegerType)

            fds += acd -> fd


            fd.body = Some(MatchExpr(e.toVariable, 
              actDef.knownCCDescendants.map { cct =>
                val fields = cct.fieldsTypes.map ( t => FreshIdentifier("field", t))

                val rhs = fields.foldLeft(InfiniteIntegerLiteral(1): Expr) { (i, f) =>
                  plus(i, sizeFor(f.toVariable))
                }

                MatchCase(CaseClassPattern(None, cct, fields.map(f => WildcardPattern(Some(f)))), None, rhs)
              }
            ))

            fd
          })

          FunctionInvocation(fd.typed(tps), Seq(of)) 

        case tt @ TupleType(tps) =>
          val exprs = for ((t,i) <- tps.zipWithIndex) yield {
            sizeFor(tupleSelect(of, i+1, tps.size))
          }

          exprs.foldLeft(InfiniteIntegerLiteral(1): Expr)(plus)

        case _ =>
          InfiniteIntegerLiteral(1)
      }

      val sizeOf = sizeFor(tupleWrap(ins.map(_.toVariable)))

      // We need to synthesize a size function for ins' types.
      val pgm1 = Program(pgm.units :+ UnitDef(FreshIdentifier("new"), List(
        ModuleDef(FreshIdentifier("new"), fds.values.toSeq, false)
      )))

      val modelEnum = new ModelEnumerator(ctx, pgm1, sf)

      val enum = modelEnum.enumVarying(ins, satisfying, sizeOf, 5)

      enum.take(maxValid).map(model => ins.map(model)).takeWhile(_ => !interrupted.get)
    }
  }

}
