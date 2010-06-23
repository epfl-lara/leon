package orderedsets

import AST._
import Phase3._

object Reconstruction {
  // Reconstruction aimed at getting the smallest model
  import scala.collection.mutable.Map

  class ReconstructionImpossible(s: String) extends Exception(s);
  private def fail(msg: String) = throw new ReconstructionImpossible(msg)

  // The output type
  case class ReconstructedValues(int: Map[Symbol, Int], sets: Map[Symbol, Set[Int]]);

  // The Beta variables
  class Beta(val pij: Set[Symbol], val size: Int) {
    var set: Set[Int] = Set.empty

    def isFull = set.size >= size

    def isEmpty = size == 0

    def insert(i: Int) = {
      set += i
      if (set.size > size) error("Venn size exceeded")
    }

    override def toString = "Pijs=" + pij.toString + "\n" + "Len = " + size + " \nSet = " + set + "\n"
  }

  object Beta {
    def unapply(obj: Beta): Option[(Set[Symbol], Int, Set[Int])] = Some(obj.pij, obj.size, obj.set)
  }

  // This function puts the inf and the sup in the correct
  // Venn Regions
  def populate(betas: Array[Beta], sets: List[Symbol], elem: Int): Unit = {
    /*
    for (ii <- 0 until betas.length) {
      val Beta(pij, size, _) = betas(ii)

      // Determine whether this beta is included in all the regions
      //var invalid = false
      //sets.foreach(s => (invalid = invalid || !pij(s)))
      val valid = (sets forall pij)


      // If this beta's venn region is contained in all the sets
      // and the predicted size is > 0, then use this region
      if (valid && betas(ii).isNonEmpty) {
        betas(ii).insert(elem)
        return
      }
    }
    throw (new ReconstructionImpossible("INF or SUP cannot be in this equivClass!!"))
    */

    // Here's the functional version :P
    betas find {beta => !beta.isFull && (sets forall beta.pij)} match {
      case Some(beta) => beta insert elem
      case None =>
        println(sets)
        betas foreach {println(_)}
        fail("INF or SUP cannot be in this equivClass!!")
    }
  }

  // Return the union of all the VennRegions contained in the setVar
  def getUnionOfVennRegions(betas: Array[Beta], setVar: Symbol) = {
    /*
    var constructedSet: Set[Int] = Set.empty
    for (ii <- 0 until betas.length) {
      val Beta(pij, _, set) = betas(ii)
      constructedSet ++= (if (pij(setVar)) set else Set.empty)
    }*/
    val containedSets = for (Beta(pij, _, set) <- betas; if pij(setVar)) yield set
    (Set.empty[Int] /: containedSets)(_ ++ _)
  }

  // Main function to call
  def getReconstruction(z3Out: Sat, outSetVars: List[Symbol], outIntVar: List[Symbol], eqCls: List[EquiClass]) = {
    val Sat(deleteModel, boolZ3Values, intZ3Values) = z3Out
    var outIntMap: Map[Symbol, Int] = Map()
    var outSetMap: Map[Symbol, Set[Int]] = Map()

    def boolVal(sym: Symbol) = boolZ3Values(sym)
    def intVal(sym: Symbol) = intZ3Values(sym)

    // The default values for integers is zero
    // TODO Removed default value.. Why would a variable be unmapped ?
    for (vOut <- outIntVar) outIntMap(vOut) = intVal(vOut)

    var populatedSets: Map[Symbol, Set[Int]] = Map.empty

    // Starting by making each venn region
    for (v@EquiClass(num, setWithInfsHere, _, setWithSupsHere, clsType, _) <- eqCls) {
      val setVarsInEq = v.allSets match {
        case Some(sets) => sets map {Symbol.partOf(_, num)}
        case None => fail("Forgot to initialize allsets!")
      }
      val N: Int = v.getNBound match {
        case Some(value) => value
        case None => fail("Forgot to initialize N in equivClass")
      }
      val upperBound = v.upper
      val lowerBound = v.lower

      // Populating the lengths and pij's of beta vectors
      var betas: Array[Beta] = new Array(N)
      for (ii <- 1 to N) {
        var boolPValues: Set[Symbol] = Set.empty
        for (set <- setVarsInEq) {
          val pij = Symbol.beta(ii, TermVar(set))
          // The default value for a venn region is empty
          if (boolVal(pij))
            boolPValues += set
        }

        // The ll.x variable
        val ll_ii = Symbol.vennSize(ii, v.num)
        betas(ii - 1) = new Beta(boolPValues, intVal(ll_ii))
      }

      var lb = lowerBound match {
        case Excl(intVars) => intVal(intVars.head) + 1 //getOneValue(intVars) + 1
        case Incl(intVars) => intVal(intVars.head)
      //case _ => throw (new ReconstructionImpossible("Ill formed lower bound."))
      }
      var ub = upperBound match {
        case Excl(intVars) => intVal(intVars.head) - 1 // These values must be present?
        case Incl(intVars) => intVal(intVars.head)
      //case _ => throw (new ReconstructionImpossible("Ill formed upper bound."))
      }

      // Is this the unbounded set
      val wasUnbounded = clsType == Unbounded // lb > ub
      val wasSingleton = (lb == ub) // clsType == Singleton

      // Choose values for inf and sup of sets in this class
      if (!setWithInfsHere.isEmpty) {
        populate(betas, setWithInfsHere.toList.map {x => Symbol.partOf(TermVar(x), num)}, lb)
        lb += 1
      }

      if (!setWithSupsHere.isEmpty && !wasSingleton) {
        populate(betas, setWithSupsHere.toList.map {x => Symbol.partOf(TermVar(x), num)}, ub)
        ub -= 1
      }

      // Populating the Venn Regions

      for (beta <- betas) {
        if (beta.size > 100) println("Warning, large set !  Size = " + beta.size)
        while (!beta.isFull) {
          beta insert lb
          lb += 1
        }
      }
      if (!wasUnbounded && lb - 1 != ub) {
        //println("   WARNING: " +(lb-1) + " != " + ub)
        fail("lb-1 != ub : " + (lb - 1) + " != " + ub)
      }

      for (s <- setVarsInEq)
        populatedSets(s) = getUnionOfVennRegions(betas, s)
    }
    //println("Populated Sets = " + populatedSets.toString)

    for (s <- outSetVars) {
      val setSymbols = for (cls <- eqCls) yield Symbol.partOf(s, cls.num)
      val setContents = for (sym <- setSymbols; if populatedSets contains sym) yield populatedSets(sym)
      outSetMap(s) = (Set.empty[Int] /: setContents) {_ ++ _}
    }

    ReconstructedValues(outIntMap, outSetMap)
  }
}
