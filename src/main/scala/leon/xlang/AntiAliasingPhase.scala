/* Copyright 2009-2015 EPFL, Lausanne */

package leon.xlang

import leon.TransformationPhase
import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.ExprOps._
import leon.purescala.DefOps._
import leon.purescala.Extractors.IsTyped
import leon.purescala.Types._
import leon.purescala.Constructors._
import leon.xlang.Expressions._

object AntiAliasingPhase extends TransformationPhase {

  val name = "Anti-Aliasing"
  val description = "Make aliasing explicit"

  override def apply(ctx: LeonContext, pgm: Program): Program = {

    var updatedFunctions: Map[FunDef, (FunDef, Seq[ValDef])] = Map()

    for {
      fd <- pgm.definedFunctions
    } {
      updateFunDef(fd).foreach{ case (nfd, mvs) => {
        updatedFunctions += (fd -> ((nfd, mvs)))
      }}
    }
    println(updatedFunctions)

    for {
      fd <- pgm.definedFunctions
    } {
      fd.body = fd.body.map(bd => updateInvocations(bd, updatedFunctions))
    }

    val res = replaceFunDefs(pgm)(fd => updatedFunctions.get(fd).map(_._1), (fi, fd) => None)
    println(res._1)
    res._1
  }

  private def updateInvocations(body: Expr, updatedFunctions: Map[FunDef, (FunDef, Seq[ValDef])]): Expr = {
    val freshBody = postMap {
      case fi@FunctionInvocation(fd, args) => updatedFunctions.get(fd.fd).map{ case (nfd, modifiedParams) => {
        val modifiedArgs: Seq[Variable] = 
          args.zip(fd.params)
              .filter(p => modifiedParams.contains(p._2))
              .map(_._1.asInstanceOf[Variable])

        val freshRes = FreshIdentifier("res", nfd.returnType)

        val extractResults = Block(
          modifiedArgs.zipWithIndex.map(p => Assignment(p._1.id, TupleSelect(freshRes.toVariable, p._2 + 2))),
          TupleSelect(freshRes.toVariable, 1))


        Let(freshRes, FunctionInvocation(nfd.typed, args).setPos(fi), extractResults)
      }}
      case _ => None
    }(body)

    freshBody
  }

  private def updateFunDef(fd: FunDef): Option[(FunDef, Seq[ValDef])] = {
    var isAliasing = false
    //TODO: in the future, any object with vars could be aliased and so
    //      we will need a general property

    val aliasedParams: Seq[Identifier] = 
      fd.params.filter(vd => vd.getType match {
        case ArrayType(_) => {
          fd.body.exists(body => {
            exists{
              case ArrayUpdate(Variable(a), _, _) => a == vd.id
              case _ => false
            }(body)
          })
        }
        case _ => false
      }).map(_.id)


    if(aliasedParams.isEmpty) None else {
      val freshLocalVars: Seq[Identifier] = aliasedParams.map(v => v.freshen)
      val rewritingMap: Map[Identifier, Identifier] = aliasedParams.zip(freshLocalVars).toMap

      val newBody = fd.body.map(body => {

        val freshBody = postMap {
          case au@ArrayUpdate(a, i, v) =>
            val Variable(id) = a
            rewritingMap.get(id).map(freshId =>
              Assignment(freshId, ArrayUpdated(freshId.toVariable, i, v).setPos(au)).setPos(au)
            )
          case _ => None
          //case as@ArraySelect(a, i) =>

          //case l@Let(i, IsTyped(v, ArrayType(_)), b) =>
          //  LetVar(i, v, b).setPos(l)
        }(body)

        val freshBody2 = replaceFromIDs(rewritingMap.map(p => (p._1, p._2.toVariable)), freshBody) 

        //WARNING: only works if side effects in Tuples are extracted from left to right,
        //         in the ImperativeTransformation phase.
        val finalBody: Expr = Tuple(freshBody2 +: freshLocalVars.map(_.toVariable))

        freshLocalVars.zip(aliasedParams).foldLeft(finalBody)((bd, vp) => {
          LetVar(vp._1, Variable(vp._2), bd)
        })

      })

      val newReturnType: TypeTree = {
        tupleTypeWrap(fd.returnType +: freshLocalVars.map(_.getType))
      }

      val newPostcondition = fd.postcondition.map(post => {
        val Lambda(Seq(res), postBody) = post
        val newRes = ValDef(FreshIdentifier(res.id.name, newReturnType))
        val newBody =
          replace(
            aliasedParams.zipWithIndex.map{ case (id, i) => 
              (id.toVariable, TupleSelect(newRes.toVariable, i+2)): (Expr, Expr)}.toMap +
            (res.toVariable -> TupleSelect(newRes.toVariable, 1)),
          postBody)
        Lambda(Seq(newRes), newBody).setPos(post)
      })

      val newFunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, newReturnType)
      newFunDef.addFlags(fd.flags)
      newFunDef.body = newBody
      newFunDef.precondition = fd.precondition
      newFunDef.postcondition = newPostcondition

      Some((newFunDef, aliasedParams.map(id => ValDef(id))))
    }
  }


  //private def rec(expr: Expr): Expr = {
  //  simplePostTransform {
  //    case fi@FunctionInvocation(tfd, args) =>
  //      

  //  }(expr)
  //}

  
  /*
   * It seems ArrayTransformation is really a solution to local aliasing, by changing
   * val to var. This AntiAliasingPhase should try to generalize this solution
   * accross function calls.
   */

}
