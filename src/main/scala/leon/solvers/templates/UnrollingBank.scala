/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package solvers
package templates

import utils._
import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import evaluators._

class UnrollingBank[T](reporter: Reporter, templateGenerator: TemplateGenerator[T]) {
  implicit val debugSection = utils.DebugSectionSolver

  private val encoder = templateGenerator.encoder

  // Keep which function invocation is guarded by which guard,
  // also specify the generation of the blocker.
  private var blockersInfoStack = List[Map[T, (Int, Int, T, Set[TemplateCallInfo[T]])]](Map())

  // Function instantiations have their own defblocker
  private var defBlockers       = Map[TemplateCallInfo[T], T]()

  def blockersInfo = blockersInfoStack.head

  def blockersInfo_= (v: Map[T, (Int, Int, T, Set[TemplateCallInfo[T]])]) = {
    blockersInfoStack = v :: blockersInfoStack.tail
  }

  def push() {
    blockersInfoStack = blockersInfo :: blockersInfoStack
  }

  def pop(lvl: Int) {
    blockersInfoStack = blockersInfoStack.drop(lvl)
  }

  def dumpBlockers = {
    blockersInfo.groupBy(_._2._1).toSeq.sortBy(_._1).foreach { case (gen, entries) =>
      reporter.debug("--- "+gen)


      for (((bast), (gen, origGen, ast, fis)) <- entries) {
        reporter.debug(f".     $bast%15s ~> "+fis.mkString(", "))
      }
    }
  }

  def canUnroll = !blockersInfo.isEmpty

  def currentBlockers = blockersInfo.map(_._2._3)

  def getBlockersToUnlock: Seq[T] = {
    if (!blockersInfo.isEmpty) {
      val minGeneration = blockersInfo.values.map(_._1).min

      blockersInfo.filter(_._2._1 == minGeneration).toSeq.map(_._1)
    } else {
      Seq()
    }
  }

  private def registerBlocker(gen: Int, id: T, fis: Set[TemplateCallInfo[T]]) {
    val notId = encoder.not(id)

    blockersInfo.get(id) match {
      case Some((exGen, origGen, _, exFis)) =>
        // PS: when recycling `b`s, this assertion becomes dangerous.
        // It's better to simply take the max of the generations.
        // assert(exGen == gen, "Mixing the same id "+id+" with various generations "+ exGen+" and "+gen)

        val minGen = gen min exGen

        blockersInfo += id -> (minGen, origGen, notId, fis++exFis)
      case None =>
        blockersInfo += id -> (gen, gen, notId, fis)
    }
  }

  def getClauses(expr: Expr, bindings: Map[Expr, T]): Seq[T] = {
    // OK, now this is subtle. This `getTemplate` will return
    // a template for a "fake" function. Now, this template will
    // define an activating boolean...
    val template = templateGenerator.mkTemplate(expr)


    val trArgs = template.tfd.params.map(vd => bindings(Variable(vd.id)))

    // ...now this template defines clauses that are all guarded
    // by that activating boolean. If that activating boolean is 
    // undefined (or false) these clauses have no effect...
    val (newClauses, newBlocks) =
      template.instantiate(template.trActivatingBool, trArgs)

    for((i, fis) <- newBlocks) {
      registerBlocker(nextGeneration(0), i, fis)
    }
    
    // ...so we must force it to true!
    template.trActivatingBool +: newClauses
  }

  def nextGeneration(gen: Int) = gen + 3

  def decreaseAllGenerations() = {
    for ((block, (gen, origGen, ast, finvs)) <- blockersInfo) {
      // We also decrease the original generation here
      blockersInfo += block -> (math.max(1,gen-1), math.max(1,origGen-1), ast, finvs)
    }
  }

  def promoteBlocker(b: T) = {
    if (blockersInfo contains b) {
      val (gen, origGen, ast, fis) = blockersInfo(b)
      
      blockersInfo += b -> (1, origGen, ast, fis)
    }
  }

  def unrollBehind(ids: Seq[T]): Seq[T] = {
    assert(ids.forall(id => blockersInfo contains id))

    var newClauses : Seq[T] = Seq.empty

    for (id <- ids) {
      val (gen, _, _, fis) = blockersInfo(id)

      blockersInfo = blockersInfo - id

      var reintroducedSelf = false

      for (fi <- fis) {
        var newCls = Seq[T]()

        val defBlocker = defBlockers.get(fi) match {
          case Some(defBlocker) =>
            // we already have defBlocker => f(args) = body
            defBlocker
          case None =>
            // we need to define this defBlocker and link it to definition
            val defBlocker = encoder.encodeId(FreshIdentifier("d").setType(BooleanType))
            defBlockers += fi -> defBlocker

            val template              = templateGenerator.mkTemplate(fi.tfd)
            reporter.debug(template)
            val (newExprs, newBlocks) = template.instantiate(defBlocker, fi.args)

            for((i, fis2) <- newBlocks) {
              registerBlocker(nextGeneration(gen), i, fis2)
            }

            newCls ++= newExprs
            defBlocker
        }

        // We connect it to the defBlocker:   blocker => defBlocker
        if (defBlocker != id) {
          newCls ++= List(encoder.implies(id, defBlocker))
        }

        reporter.debug("Unrolling behind "+fi+" ("+newCls.size+")")
        for (cl <- newCls) {
        reporter.debug("  . "+cl)
        }

        newClauses ++= newCls
      }

    }

    reporter.debug(s"   - ${newClauses.size} new clauses")
    //context.reporter.ifDebug { debug =>
    //  debug(s" - new clauses:")
    //  debug("@@@@")
    //  for (cl <- newClauses) {
    //    debug(""+cl)
    //  }
    //  debug("////")
    //}

    //dumpBlockers
    //readLine()

    newClauses
  }
}
