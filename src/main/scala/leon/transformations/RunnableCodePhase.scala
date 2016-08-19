/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package transformations

import java.io.File

import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Types._
import leon._
import leon.purescala.ScalaPrinter
import leon.utils._
import invariant.util._
import Util._
import ProgramUtil._
import PredicateUtil._
import invariant.util.ExpressionTransformer._
import invariant.structure.FunctionUtils._
import invariant.util.LetTupleSimplification._

object RunnableCodePhase extends TransformationPhase {

  val name = "Runnable Code"
  val description = "Generating Scala runnable code from the instrumented code"

  def apply(ctx: LeonContext, pgm: Program): Program = {
    val debugRunnable = false

    var instFunc = Set[FunDef]()
    val funMap = pgm.definedFunctions.collect {
      case fd if fd.id.name.contains("-") =>
        val freshId = FreshIdentifier((fd.id.name).replaceAll("-",""), fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        instFunc = instFunc + newfd
        (fd -> newfd)
      case fd =>
        val freshId = FreshIdentifier(fd.id.name, fd.returnType)
        val newfd = new FunDef(freshId, fd.tparams, fd.params, fd.returnType)
        (fd -> newfd)
    }.toMap

    val cg =  CallGraphUtil.constructCallGraph(pgm, onlyBody = true)
    var reachableFunc = instFunc
    for(i <- instFunc) {
      reachableFunc = reachableFunc ++ cg.transitiveCallees(i)
    }
//    var reachableFunc = cg.transitiveCallees(Seq(instFunc))

    def removeContracts(ine: Expr, fd: FunDef): Expr = simplePostTransform{
      case FunctionInvocation(tfd, args) if funMap.contains(tfd.fd) =>
        FunctionInvocation(TypedFunDef(funMap(tfd.fd), tfd.tps), args)
      case Ensuring(body, pred) => removeContracts(body, fd)
      case Require(pred, body) => removeContracts(body, fd)
//      case Tuple(args) => {
//        args.head match {
//          case TupleSelect(v, j) if j == 1 =>
//            val success =  args.zipWithIndex.forall {
//              case (TupleSelect(u, i), index) if v == u && i == index + 1 => true
//              case _ => false
//            }
//            val tup = v.getType.asInstanceOf[TupleType]
//            if(success && (tup.dimension == args.size)) v else Tuple(args)
//          case _ => Tuple(args)
//        }
//      }
      case e => e
    }(ine)

    for ((from, to) <- funMap) {
      to.fullBody = removeContracts(from.fullBody, from)
      // we also do not copy decreases
      from.flags.foreach(to.addFlag(_)) //copy annotations
    }
//    val newprog = copyProgram(pgm, (defs: Seq[Definition]) => defs.map {
//      case fd: FunDef if funMap.contains(fd) => funMap(fd)
//      case d                                 => d
//    })
    def mapdefs(defs: Seq[Definition]): Seq[Definition] = {
      defs.collect {
        case fd:FunDef if (reachableFunc contains funMap(fd)) => funMap(fd)
        case d if !(d.isInstanceOf[FunDef]) => d
      }
    }

    val newprog = pgm.copy(units = pgm.units.collect {
      case unit if unit.defs.nonEmpty => unit.copy(defs = unit.defs.collect {
        case module: ModuleDef if module.defs.nonEmpty =>
          module.copy(defs = mapdefs(module.defs))
        case other => other
      })
    })

    if (debugRunnable)
      println("After transforming to runnable code: \n" + ScalaPrinter.apply(newprog, purescala.PrinterOptions(printRunnableCode = true)))

    val optOutputDirectory = LeonStringOptionDef("o", "Output directory", "leon.out", "dir")

    val outputFolder = ctx.findOptionOrDefault(optOutputDirectory)
    try {
      new File(outputFolder).mkdir()
    } catch {
      case _ : java.io.IOException => ctx.reporter.fatalError("Could not create directory " + outputFolder)
    }

    for (u <- newprog.units if u.isMainUnit) {
      val outputFile = s"$outputFolder${File.separator}${u.id.toString}.scala"
      try {
        import java.io.FileWriter
        import java.io.BufferedWriter
        val fstream = new FileWriter(outputFile)
        val out = new BufferedWriter(fstream)
        out.write(ScalaPrinter(u, purescala.PrinterOptions(printRunnableCode = true), opgm = Some(newprog)))
        out.close()
      }
      catch {
        case _ : java.io.IOException => ctx.reporter.fatalError("Could not write on " + outputFile)
      }
    }
    ctx.reporter.info("Output written on " + outputFolder)
    newprog
  }
}
