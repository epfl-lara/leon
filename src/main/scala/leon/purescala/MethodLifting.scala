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
  val description = "Translate methods into top-level functions"

  def apply(ctx: LeonContext, program: Program): Program = {
    // First we create the appropriate functions from methods:
    var mdToFds  = Map[FunDef, FunDef]()

    for {
      cd <- program.classHierarchyRoots
      if cd.methods.nonEmpty
      fd <- cd.methods
    } {
      // We import class type params and freshen them
      val ctParams = cd.tparams map { _.freshen }
      val tparamsMap = cd.tparams.zip(ctParams map { _.tp }).toMap

      val id = FreshIdentifier(cd.id.name+"$"+fd.id.name).setPos(fd.id)
      val recType = classDefToClassType(cd, ctParams.map(_.tp))
      val retType = instantiateType(fd.returnType, tparamsMap)
      val fdParams = fd.params map { vd =>
        val newId = FreshIdentifier(vd.id.name, instantiateType(vd.id.getType, tparamsMap))
        ValDef(newId).setPos(vd.getPos)
      }
      val paramsMap = fd.params.zip(fdParams).map{case (x,y) => (x.id, y.id)}.toMap

      val receiver = FreshIdentifier("$this", recType).setPos(cd.id)

      val nfd = new FunDef(id, ctParams ++ fd.tparams, retType, ValDef(receiver) +: fdParams, fd.defType)
      nfd.copyContentFrom(fd)
      nfd.setPos(fd)
      nfd.fullBody = instantiateType(nfd.fullBody, tparamsMap, paramsMap)

      mdToFds += fd -> nfd
    }

    def translateMethod(fd: FunDef) = {
      val (nfd, rec) = mdToFds.get(fd) match {
        case Some(nfd) =>
          (nfd, Some(() => Variable(nfd.params.head.id)))
        case None =>
          (fd, None)
      }

      nfd.fullBody = removeMethodCalls(rec)(nfd.fullBody)
      nfd
    }

    def removeMethodCalls(rec: Option[() => Expr])(e: Expr): Expr = {
      postMap{
        case th: This => 
          rec match {
            case Some(r) =>
              Some(r().setPos(th))
            case None =>
              ctx.reporter.fatalError("`this` used out of a method context?!?")
          }
        case mi @ MethodInvocation(rec, cd, tfd, args) =>
          rec match {
            case IsTyped(rec, ct: ClassType) =>
              Some(FunctionInvocation(mdToFds(tfd.fd).typed(ct.tps ++ tfd.tps), rec +: args).setPos(mi))
            case _ =>
              ctx.reporter.fatalError("MethodInvocation on a non-class receiver !?!")
          }
        case _ => None
      }(e)
    }

    val modsToMods = ( for {
      u <- program.units
      m <- u.modules
    } yield (m, {
      // We remove methods from class definitions and add corresponding functions
      val newDefs = m.defs.flatMap {
        case acd: AbstractClassDef if acd.methods.nonEmpty =>
          acd +: acd.methods.map(translateMethod)

        case ccd: CaseClassDef if ccd.methods.nonEmpty =>
          ccd +: ccd.methods.map(translateMethod)

        case fd: FunDef =>
          List(translateMethod(fd))

        case d =>
          List(d)
      }

      // finally, we clear methods from classes
      m.defs.foreach {
        case cd: ClassDef =>
          cd.clearMethods()
        case _ =>
      }
      ModuleDef(m.id, newDefs, m.isStandalone )
    })).toMap

    val newUnits = program.units map { u => u.copy(
      
      imports = u.imports flatMap {
        case s@SingleImport(c : ClassDef) =>
          // If a class is imported, also add the "methods" of this class
          s :: ( c.methods map { md => SingleImport(mdToFds(md))})
        // If importing a ModuleDef, update to new ModuleDef
        case SingleImport(m : ModuleDef) => List(SingleImport(modsToMods(m)))
        case WildcardImport(m : ModuleDef) => List(WildcardImport(modsToMods(m)))
        case other => List(other)
      },

      modules = u.modules map modsToMods

    )}

    Program(program.id, newUnits)
  }

}
