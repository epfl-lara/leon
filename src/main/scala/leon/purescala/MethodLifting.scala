/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import TypeOps.instantiateType

object MethodLifting extends TransformationPhase {

  val name = "Method Lifting"
  val description = "Translate methods into functions of the companion object"

  def apply(ctx: LeonContext, program: Program): Program = {

    // First we create the appropriate functions from methods:
    var mdToFds = Map[FunDef, FunDef]()

    val newUnits = for (u <- program.units) yield {
      var fdsOf = Map[String, Set[FunDef]]()

      // 1) Create one function for each method
      for { cd <- u.classHierarchyRoots if cd.methods.nonEmpty; fd <- cd.methods } {
        // We import class type params and freshen them
        val ctParams = cd.tparams map { _.freshen }
        val tparamsMap = cd.tparams.zip(ctParams map { _.tp }).toMap

        val id = fd.id.freshen
        val recType = classDefToClassType(cd, ctParams.map(_.tp))
        val retType = instantiateType(fd.returnType, tparamsMap)
        val fdParams = fd.params map { vd =>
          val newId = FreshIdentifier(vd.id.name, instantiateType(vd.id.getType, tparamsMap))
          ValDef(newId).setPos(vd.getPos)
        }
        val paramsMap = fd.params.zip(fdParams).map{case (x,y) => (x.id, y.id)}.toMap

        val receiver = FreshIdentifier("this", recType).setPos(cd.id)

        val nfd = new FunDef(id, ctParams ++ fd.tparams, retType, ValDef(receiver) +: fdParams, fd.defType)
        nfd.copyContentFrom(fd)
        nfd.setPos(fd)
        nfd.fullBody = postMap{
          case This(ct) if ct.classDef == cd => Some(receiver.toVariable)
          case _ => None
        }(instantiateType(nfd.fullBody, tparamsMap, paramsMap))

        mdToFds += fd -> nfd
        fdsOf += cd.id.name -> (fdsOf.getOrElse(cd.id.name, Set()) + nfd)
      }

      // 2) Place functions in existing companions:
      val defs = u.defs map {
        case md: ModuleDef if fdsOf contains md.id.name =>
          val fds = fdsOf(md.id.name)
          fdsOf -= md.id.name
          ModuleDef(md.id, md.defs ++ fds, false)
        case d => d
      }

      // 3) Create missing companions
      val newCompanions = for ((name, fds) <- fdsOf) yield {
        ModuleDef(FreshIdentifier(name), fds.toSeq, false)
      }

      // 4) Remove methods in classes
      for (cd <- u.definedClasses) {
        cd.clearMethods
      }

      u.copy(defs = defs ++ newCompanions)
    }

    val pgm = Program(newUnits)

    // 5) Replace method calls with function calls
    for (fd <- pgm.definedFunctions) {
      fd.fullBody = postMap{
        case mi @ MethodInvocation(IsTyped(rec, ct: ClassType), cd, tfd, args) =>
          Some(FunctionInvocation(mdToFds(tfd.fd).typed(ct.tps ++ tfd.tps), rec +: args).setPos(mi))
        case _ => None
      }(fd.fullBody)
    }

    pgm
  }

}
