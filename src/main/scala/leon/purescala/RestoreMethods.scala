/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package purescala

import Definitions._
import Expressions._
import ExprOps.replaceFromIDs
import DefOps.replaceFunDefs
import Types._

object RestoreMethods extends TransformationPhase {

  val name = "Restore methods"
  val description = "Restore methods that were previously turned into standalone functions"

  // @TODO: This code probably needs fixing, but is mostly unused and completely untested.
  def apply(ctx: LeonContext, p: Program) = {

    val classMethods = p.definedFunctions.groupBy(_.methodOwner).collect {
      case (Some(cd: ClassDef), fds) => cd -> fds
    }

    val fdToMd = for( (cd, fds) <- classMethods; fd <- fds) yield {
      val md = fd.duplicate(tparams = fd.tparams.drop(cd.tparams.size), params = fd.params.tail)

      val thisArg  = fd.params.head
      val thisExpr = This(thisArg.getType.asInstanceOf[ClassType])

      md.fullBody = replaceFromIDs(Map(thisArg.id -> thisExpr), fd.fullBody)

      fd -> md
    }

    // We inject methods, 
    def processClassDef(cd: ClassDef): ClassDef = {
      if (classMethods contains cd) {
        for (md <- classMethods(cd).map(fdToMd)) {
          cd.registerMethod(md)
        }
      }
      cd
    }

    val np = p.copy(units = p.units.map { u =>
      u.copy(defs = u.defs.collect {
        case md: ModuleDef =>
          md.copy(
            defs = md.defs.flatMap {
              case fd: FunDef if fdToMd contains(fd) => None
              case cd: ClassDef => Some(processClassDef(cd))
              case d => Some(d)
            }
          )
        case cd: ClassDef  =>
          processClassDef(cd)
      })
    })

    val (np2, _, _, _) = replaceFunDefs(np)(fd => None, { (fi, fd) =>
      fdToMd.get(fi.tfd.fd) match {
        case Some(md) =>
          Some(MethodInvocation(
            fi.args.head,
            fi.args.head.getType.asInstanceOf[ClassType].classDef,
            md.typed(fi.tfd.tps.takeRight(md.tparams.size)),
            fi.args.tail
          ))
        case None =>
          None
      }
    })

    np2


    //// We need a special type of transitive closure, detecting only trans. calls on the same argument
    //def transCallsOnSameArg(fd : FunDef) : Set[FunDef] = {
    //  require(fd.params.length == 1)
    //  require(fd.params.head.getType.isInstanceOf[ClassType])
    //  def callsOnSameArg(fd : FunDef) : Set[FunDef] = {
    //    val theArg = fd.params.head.toVariable
    //    functionCallsOf(fd.fullBody) collect { case fi if fi.args contains theArg => fi.tfd.fd } 
    //  }
    //  reachable(callsOnSameArg,fd)
    //}

    //def refreshModule(m : ModuleDef) = {
    //  val newFuns : Seq[FunDef] = m.definedFunctions diff fd2MdFinal.keys.toSeq map substituteMethods// only keep non-methods
    //  for (cl <- m.definedClasses) {
    //    // We're going through some hoops to ensure strict fields are defined in topological order

    //    // We need to work with the functions of the original program to have access to CallGraph
    //    val (strict, other) = whoseMethods.getOrElse(cl,Seq()).partition{ fd2MdFinal(_).canBeStrictField }
    //    val strictSet = strict.toSet
    //    // Make the call-subgraph that only includes the strict fields of this class 
    //    val strictCallGraph = strict.map { st => 
    //      (st, transCallsOnSameArg(st) & strictSet)
    //    }.toMap
    //    // Topologically sort, or warn in case of cycle
    //    val strictOrdered = topologicalSorting(strictCallGraph) fold (
    //      cycle => {
    //        ctx.reporter.warning(
    //          s"""|Fields
    //              |${cycle map {_.id} mkString "\n"} 
    //              |are involved in circular definition!""".stripMargin
    //        )
    //        strict
    //      },
    //      r => r
    //    )

    //    for (fun <- strictOrdered ++ other) { 
    //      cl.registerMethod(fd2MdFinal(fun)) 
    //    }
    //  }
    //  m.copy(defs = m.definedClasses ++ newFuns).copiedFrom(m)    
    //}
  }
}
