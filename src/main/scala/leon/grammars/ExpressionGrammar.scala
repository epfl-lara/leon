/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package grammars

import purescala.Expressions._
import purescala.Definitions._
import purescala.TypeOps._
import purescala.Types._
import purescala.Common._
import utils.MapUtils

case class GenericProd(
  tparams: Seq[TypeParameterDef],
  label: Label,
  args: Seq[TypeTree],
  builder: Map[TypeParameter, TypeTree] => ProductionRule[Label, Expr]
)

/** Represents a context-free grammar of expressions */
abstract class ExpressionGrammar {

  type Prod = ProductionRule[Label, Expr]

  def generateProductions(implicit ctx: LeonContext): Seq[GenericProd]

  private[this] var genericProductions: Seq[GenericProd] = Nil

  private[this] var productions:      Map[Label, Seq[Prod]] = Map()
  private[this] var productionsCache: Map[Label, Seq[Prod]] = Map()

  /** The (cached) list of production rules for this grammar for a given nonterminal.
    *
    * @param lab The nonterminal for which production rules will be generated
    * @note This is the cached version of [[generateProductions]]. Clients should use this method.
    */

  def getProductions(lab: Label)(implicit ctx: LeonContext) = {
    productionsCache.getOrElse(lab, {
      val ps = generateProductions(lab)
      productionsCache += lab -> ps
      ps
    })
  }

  private def init()(implicit ctx: LeonContext) {
    val allProds = generateProductions

    val (static0, generic) = allProds.partition(_.tparams.isEmpty)

    val static = static0.map { gp => gp.label -> gp.builder(Map()) }

    productions = MapUtils.seqToMap(static)
    genericProductions = generic

    // this is an under-approximation, since we assume subtrees have minCost 1.
    minCosts = for ((l, ps) <- productions) yield {
      l.getType -> ps.map(p => 1 + p.subTrees.size).min
    }
  }

  var instantiations = Map[GenericProd, Set[Map[TypeParameter, TypeTree]]]().withDefaultValue(Set())

  def instantiateGenerics(lab: Label, maxSize: Int)(implicit ctx: LeonContext) = {

    val tpe = lab.getType

    //println
    //println("%"*80);
    //println(s"Instantiating ${tpe.asString} |$maxSize|");
    //println
    //println

    //println("Pool of types: ");
    //for (t <- discoveredTypes.toSeq.sortBy(_.asString)) {
    //  println(" - "+t.asString)
    //}
    //println

    for(gp <- genericProductions if (gp.args.size + 1) < maxSize) {
      //println("Looking at "+Console.BOLD+gp.retType.asString+Console.RESET+" ::= "+genProdAsString(gp))

      instantiation_<:(gp.label.tpe, tpe) match {
        case Some(tmap0) =>
          val free = gp.tparams.map(_.tp) diff tmap0.keySet.toSeq

          val tmaps = if (free.nonEmpty) {
            // Instantiate type parameters not constrained by the return value
            // of `fd`
            //
            // e.g.:
            // def countFilter[T](x: List[T], y: T => Boolean): BigInt
            //
            // We try to find instantiation of T such that arguments have
            // candidates
            //

            // Step 1. We identify the type patterns we need to match:
            // e.g. (List[T], T => Boolean)
            val pattern0 = gp.args.distinct

            val baseQuota = maxSize - tmap0.values.map(tpe =>
              minCosts.getOrElse(tpe, maxSizeFor.getOrElse(tpe, 0) + 1)
            ).sum - 1

            instantiateTypePattern(pattern0, free, baseQuota, tmap0).keySet
          } else {
            List(tmap0)
          }

          // All type params are constrained
          val tmaps1 = tmaps.filter(_.size == gp.tparams.size)

          val existing = instantiations(gp)

          // We only consider new instantiations
          val tmaps2 = tmaps1.filter(m => !existing(m))

          if (tmaps2.nonEmpty) {
            instantiations += gp -> (existing ++ tmaps2)
          }

          val prods = for (tmap <- tmaps2) yield {
            val prod = gp.builder(tmap)

            //println("    - "+prodAsString(prod))

            prod
          }

          productions += lab -> (productions.getOrElse(lab, Nil) ++ prods)

        case _ =>
      }
    }
  }

  private[this] var minCosts = Map[TypeTree, Int]()
  private[this] var newTypes = Set[TypeTree]()

  /**
   * Instantiates a type pattern, under constraints:
   * pattern: e.g. (T, U, List[T,U])
   * quota: max of the min-cost to discover
   * tmap: initial fixed type-map.
   *
   * Returns a set of type assignment with associated min-cost:
   *  e.g. Map(T -> Int, U -> Bool) -> 3
   */
  def instantiateTypePattern(
    pattern: Seq[TypeTree],
    freeTps: Seq[TypeParameter],
    quota: Int,
    tmap: Map[TypeParameter, TypeTree]
  ): Map[Map[TypeParameter, TypeTree], Int] = {

    val targetSize = freeTps.size + tmap.size

    if (quota <= 0) {
      return Map()
    }

    def availableTypes(quota: Int) = {

      val res = minCosts.flatMap { case (t, mc) =>
        if (quota >= mc) {
          Some((t, quota - mc))
        } else {
          None
        }
      }

      res
    }

    def discover(tp: TypeParameter, tmaps: Map[Map[TypeParameter, TypeTree], Int]): Map[Map[TypeParameter, TypeTree], Int] = {
      for {
        (map0, q0) <- tmaps
        p1 = pattern.map(instantiateType(_, map0))
        p <- p1
        (t, q1) <- availableTypes(q0)
        map1 <- unify(p, t, Seq(tp))
      } yield {
        (map0 ++ map1, q1)
      }
    }

    var tmaps = Map(tmap -> quota)

    for (f <- freeTps) {
      tmaps = discover(f, tmaps)
    }

    var res = Map[Map[TypeParameter, TypeTree], Int]()

    for ((tmap, qLeft) <- tmaps if tmap.size == targetSize) {
      val mc = quota - qLeft

      if (res contains tmap) {
        res += tmap -> Math.min(mc, res(tmap))
      } else {
        res += tmap -> mc
      }
    }

    res
  }

  def discoverTypes(maxSize: Int)(implicit ctx: LeonContext) = {
    for(discoverySize <- 1 to maxSize) {
      //println
      //println("#"*80);
      //println(s"Discovering Types |$discoverySize|%%%%%%");
      //println
      //println

      newTypes = Set()

      //println("Pool of types: ");
      for ((t, mc) <- minCosts.toSeq.sortBy { case (t, mc) => (mc, t.asString) }) {
        //println(" - |"+mc+"|  "+t.asString)
      }
      //println

      for(gp <- genericProductions) {
        //println("Looking at "+Console.BOLD+gp.retType.asString+Console.RESET+" ::= "+genProdAsString(gp))

        val freeTps = typeParamsOf(gp.label.tpe) intersect gp.tparams.map(_.tp).toSet

        // Step 1. We identify the type patterns we need to match:
        // e.g. (List[T], T => Boolean)
        val pattern0 = gp.args.distinct

        val tmaps = instantiateTypePattern(pattern0, freeTps.toSeq, discoverySize-1, Map())

        val retTypes = for ((tmap, minCost) <- tmaps) yield {
          (instantiateType(gp.label.tpe, tmap), minCost+1)
        }

        for ((t, mc) <- retTypes) {
          if (!(minCosts contains t)) {
            //println(" -> "+t.asString)

            minCosts += t -> mc
            newTypes += t
          }
        }
      }

      //println
      //println("New Pool of types: ");
      //for ((t, mc) <- minCosts.toSeq.sortBy { case (t, mc) => (mc, t.asString) }) {
      //  val isNew = if(newTypes contains t) "*" else " "

      //  println(" - "+isNew+" |"+mc+"|  "+t.asString)
      //}
      //println
    }
  }

  private def applyAspects(lab: Label, prods: Seq[Prod])(implicit ctx: LeonContext): Seq[Prod] = {
    // Filter/Expand based on aspects of lab
    lab.aspects.foldLeft(prods) {
      case (ps, a) => a.applyTo(lab, ps)
    }
  }

  private def filterImpossibleCosts(lab: Label, prods: Seq[Prod]): Seq[Prod] = {
    labelSize(lab) match {
      case Some(size) =>
        prods.filter{ p =>
          p.subTrees.forall(lab => labelSize(lab).get >= minCosts.getOrElse(lab.getType, 1))
        }

      case _ =>
        prods
    }
  }

  private def computeCostsAndLogProbs(prods: Seq[Prod]): Seq[Prod] = {
    if (prods.isEmpty) {
      Nil
    } else if (prods.size == 1) {
      prods.map(_.copy(cost = 1))
    } else {
      val costs = prods map (_.cost)
      val totalCost = costs.sum
      // log(prob) = log(cost/Σ(costs))
      val logProbs = costs.map(cost => Math.log(cost.toDouble/totalCost.toDouble))
      val maxLogProb = logProbs.max

      for ((p, logProb) <- prods zip logProbs) yield {
        // cost = normalized log prob.
        val cost = (logProb/maxLogProb).round.toInt
        p.copy(cost = cost, logProb = logProb)
      }
    }
  }


  private def labelSize(lab: Label): Option[Int] = {
    lab.aspect(SizedAspectKind).collect { case aspects.Sized(size, _) => size }
  }


  private[this] var initialized = false

  private[this] var maxSizeFor = Map[TypeTree, Int]().withDefaultValue(0)

  private def generateProductions(lab: Label)(implicit ctx: LeonContext): Seq[Prod] = {
    val tpe = lab.getType

    if (!initialized) {
      init()
      initialized = true
    }

    val simpleLab = lab.stripAspects

    labelSize(lab) match {
      case Some(size) =>
        if (size > maxSizeFor(tpe)) {
          instantiateGenerics(simpleLab, size)
          maxSizeFor += tpe -> size
        }

      case None =>
        if (!(maxSizeFor contains tpe)) {
          instantiateGenerics(simpleLab, 999)
          maxSizeFor += tpe -> 1
        }
    }

    val prods1 = productions.getOrElse(simpleLab, Nil)

    val prods2 = applyAspects(lab, prods1)

    val prods3 = filterImpossibleCosts(lab, prods2)

    val prods4 = computeCostsAndLogProbs(prods3)

    prods4
  }

  private def lineize(ss: Traversable[String]): String = {
    ss.mkString("\n" + " " * 55)
  }

  def prodAsString(p: Prod)(implicit ctx: LeonContext): String = {
    val subs = p.subTrees.map { t =>
      FreshIdentifier(Console.BOLD + t.asString + Console.RESET, t.getType).toVariable
    }

    f"(${p.cost}%3d, ${p.logProb}%2.3f) " + lineize(p.builder(subs).asString.lines.toSeq)
  }

  def genProdAsString(gp: GenericProd)(implicit ctx: LeonContext): String = {
    val tmap = gp.tparams.map(tpd => tpd.tp -> tpd.tp).toMap

    val prod = gp.builder(tmap)

    val tps = Console.GREEN+gp.tparams.map(_.asString).mkString("[", ",", "]")+Console.RESET

    tps+" "+prodAsString(prod)
  }

  def asString(implicit ctx: LeonContext): String = {
    def sorter(lp1: (Label, Seq[Prod]), lp2: (Label, Seq[Prod])): Boolean = {
      val l1 = lp1._1
      val l2 = lp2._1

      val os1 = labelSize(l1)
      val os2 = labelSize(l2)

      (os1, os2) match {
        case (Some(s1), Some(s2)) =>
          if (s1 > s2) {
            true
          } else if (s1 == s2) {
            l1.asString < l2.asString
          } else {
            false
          }
        case _ => l1.asString < l2.asString
      }
    }

    val res = new scala.collection.mutable.StringBuilder()

    res.append("\n --- Productions: ---\n")

    for ((lab, ps) <- productions.toSeq.sortWith(sorter)) {

      val lhs = f"${Console.BOLD}${lab.asString}%50s${Console.RESET} ::= "

      if (ps.isEmpty) {
        res.append(lhs + "ε\n")
      } else {
        res.append(lhs + lineize(ps.map(prodAsString))+"\n")
      }
    }

    for ((tpe, ps) <- genericProductions.groupBy(_.label.tpe)) {
      val lhs = f"${Console.BOLD}${tpe.asString}%50s${Console.RESET} ::= "
      res.append(lhs + lineize(ps.map(genProdAsString))+"\n")
    }

    res.append("\n --- Computed Productions: ---\n")

    for ((lab, ps) <- productionsCache.toSeq.sortWith(sorter)) {

      val lhs = f"${Console.BOLD}${lab.asString}%50s${Console.RESET} ::= "

      if (ps.isEmpty) {
        res.append(lhs + "ε\n")
      } else {
        res.append(lhs + lineize(ps.map(prodAsString))+"\n")
      }
    }

    res.toString
  }

  /** Generates a [[ProductionRule]] without nonterminal symbols */
  def terminal(
      label: Label,
      builder: => Expr,
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      weight: Double = -1.0) = {

    GenericProd(Nil, label, Nil, tmap => ProductionRule[Label, Expr](Nil, { (subs: Seq[Expr]) => builder }, tag, cost, weight))
  }

  /** Generates a [[ProductionRule]] with nonterminal symbols */
  def nonTerminal(
      label: Label,
      subs: Seq[Label],
      builder: (Seq[Expr] => Expr),
      tag: Tags.Tag = Tags.Top,
      cost: Int = 1,
      weight: Double = -1.0) = {

    GenericProd(Nil, label, Nil, tmap => ProductionRule[Label, Expr](subs, builder, tag, cost, weight))
  }
}
