/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

object ADTInvariants extends TransformationPhase {

  val name = "ADT Invariants"
  val description = "Make sure ADT invariants are asserted at all necessary points"

  def apply(ctx: LeonContext, program: Program): Program = {

    var cdToInvariant : Map[ClassDef, FunDef] = Map.empty
    var cdToWrapper   : Map[ClassDef, FunDef] = Map.empty

    val pgm = program.definedFunctions.filter(_.isInvariant).foldLeft(program) { case (pgm, fd) =>
      val cd = fd.methodOwner.get
      val thisId = fd.params.head.id
      cdToInvariant += cd -> fd

      val wrapper = new FunDef(FreshIdentifier("wrapper", cd.typed, true), fd.tparams, fd.params, cd.typed)
      wrapper.addFlag(IsADTInvariant)
      cdToWrapper += cd -> wrapper

      val res = FreshIdentifier("res", cd.typed)
      wrapper.fullBody = Ensuring(Variable(thisId),
        Lambda(Seq(ValDef(res)), FunctionInvocation(fd.typed, Seq(Variable(thisId)))))

      def rec(expr: Expr, seen: Set[FunDef]): Expr = expr match {
        case FunctionInvocation(tfd, args) if args.contains(Variable(thisId)) =>
          if (seen(tfd.fd)) {
            throw LeonFatalError("ADT invariant has potentially infinite unfoldings referring to 'this'")
          } else tfd.body match {
            case Some(body) =>
              val newBody = replaceFromIDs((tfd.params.map(_.id) zip args).toMap, body)
              rec(newBody, seen + tfd.fd)
            case None => expr
          }

        case CaseClassSelector(_, Variable(`thisId`), _) =>
          expr

        case Variable(`thisId`) =>
          throw LeonFatalError("Unexpected reference to 'this' in ADT invariant")

        case Operator(es, recons) => recons(es.map(rec(_, seen)))
      }

      fd.body = fd.body.map(rec(_, Set.empty))

      DefOps.addFunDefs(pgm, Seq(wrapper), fd)
    }

    for (fd <- pgm.definedFunctions) {
      val invClass = fd.methodOwner.filter(_ => fd.isInvariant)
      val invArg = invClass.map(_ => Variable(fd.params.head.id))

      fd.fullBody = postMap {
        case CaseClassSelector(cct, receiver, field) =>
          if (invArg == Some(receiver)) {
            None
          } else cdToWrapper.get(cct.classDef.root) match {
            case Some(fd) =>
              val wrapped = FunctionInvocation(fd.typed(cct.tps), Seq(receiver))
              Some(CaseClassSelector(cct, wrapped, field))
            case None => None
          }

        case cc @ CaseClass(cct, args) =>
          cdToInvariant.get(cct.classDef.root) match {
            case Some(fd) =>
              val adt = FreshIdentifier("adt", cct, true)
              Some(Let(adt, cc, Assert(
                FunctionInvocation(fd.typed(cct.tps), Seq(Variable(adt))),
                Some("ADT Invariant was broken @" + cc.getPos),
                Variable(adt)
              ).setPos(cc)).setPos(cc))
            case None => None
          }

        case _ => None
      } (fd.fullBody)
    }

    pgm
  }
}
