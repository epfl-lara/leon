package orderedsets

import scala.collection.mutable.{ArrayBuffer, HashMap => MutableMap, HashSet => MutableSet, ListBuffer}
import AST._
import ASTUtil._
import Primitives._
import GuessOrdering._

object EquiClassPartition {

  /**Split formula in PA and cardinality parts **/

//   private type CardSplit = (Term, Int => Term)
//
//   private def split(formula: Formula, numC: Int): (Formula, List[CardSplit]) = {
//     val cards = new ListBuffer[CardSplit]
//
//     def splitForm(form: Formula): Formula = form match {
//       case True | False | PropVar(_) => form
//       case And(fs) => And(fs map splitForm)
//       case Or(fs) => Or(fs map splitForm)
//       case Not(f) => Not(splitForm(f))
//       case Predicate(EQ, List(Op(CARD, List(set)), zero@Lit(IntLit(0)))) =>
//         cards += ((set, _ => zero))
//         True
//       case Predicate(cond, ts) => Predicate(cond, ts map splitTerm)
//     }
//     def splitTerm(term: Term): Term = term match {
//       case Lit(_) | TermVar(_) => term
//       case Op(CARD, List(set)) =>
//         val auxVars = List.tabulate(numC)((_: Int) => TermVar(Symbol.freshInt))
//         val auxFun = auxVars.toArray
//         cards += ((set, auxFun.apply))
//         Op(ADD, auxVars)
//       case Op(op, ts) => Op(op, ts map splitTerm)
//     }
//     val form = splitForm(formula)
//     (form, cards.toList)
//   }


  sealed trait Bound
  case class Incl(bvars: List[Symbol]) extends Bound
  case class Excl(bvars: List[Symbol]) extends Bound

  sealed trait ClassType
  case class Singleton(isLE: Boolean) extends ClassType
  case object Bounded extends ClassType
  case object Unbounded extends ClassType

  private var classCount = 0
  class EquiClass(val lower: Bound, val upper: Bound, val sets: List[Symbol], val classType: ClassType) {
    val num = {classCount += 1; classCount}

    var sparsenessBound: Option[Int] = None

    def getNBound = sparsenessBound

    var allSets: Option[List[Symbol]] = None

    val infSets = lower match {
      case Incl(infs) => getInfSets(infs)
      case Excl(_) => Set.empty[Symbol]
    }
    val supSets = upper match {
      case Incl(sups) => getSupSets(sups)
      case Excl(_) => Set.empty[Symbol]
    }
    val sizeTerm = ((lower, upper): @unchecked) match {
      case (Incl(low :: _), Incl(high :: _)) => high + 1 - low
      case (Incl(low :: _), Excl(high :: _)) => high - low
      case (Excl(low :: _), Incl(high :: _)) => high - low
      case (Excl(low :: _), Excl(high :: _)) => high - (low + 1)
    }
  }

  object EquiClass {
    def unapply(obj: EquiClass): Option[(Int, Set[Symbol], List[Symbol], Set[Symbol], ClassType, Term)] = {
      Some((obj.num, obj.infSets, obj.sets, obj.supSets, obj.classType, obj.sizeTerm))
    }
  }

  var orderCount = 0;
  // (continuationZ3call: (Context, Formula, List[EquiClass]) => Unit)
  def apply(z3: Context, formula: Formula, order: Order) {
    orderCount += 1
    if (order.isEmpty) {
      val zero = Symbol.freshInt
      val nnfForm = NormalForms.nnf(formula && (zero === 0))

      val allSets = setvars(nnfForm)
      val eqClass = new EquiClass(Excl(List(zero)), Excl(List(zero)), allSets.toList, Unbounded)
      eqClass.allSets = Some(allSets.toList)
        
      val classFormula = NormalForms.nnf(renameSets(eqClass.num, allSets)(nnfForm))
      z3.impose(classFormula)
      z3.impose(classSizeConstraints(eqClass, allSets))

//       val formula0 = QFBAPAtoPATranslator.rewriteSetRel(nnfForm)
//       val (paFormula, cardSplits) = split(formula0, 1)
//       def transformTerm(term: Term): Term = term match {
//         case Op(op, terms) =>
//           Op(op, terms map transformTerm)
//         case TermVar(sym) if sym.isSet =>
//           TermVar(Symbol.partOf(sym, equiCls.num))
//         case _ => term
//       }
//       val bapaBuffer = new ListBuffer[Formula]
//       for ((setExpr, nameGen) <- cardSplits)
//         bapaBuffer += transformTerm(setExpr).card === nameGen(0)
//       
//       val bapaForm = NormalForms.nnf(And(bapaBuffer.toList))
//       val (paForm, n) = QFBAPAtoPATranslator(bapaForm, equiCls.num)
//       
//       equiCls.sparsenessBound = Some(n)
//       equiCls.allSets = Some(setvars(nnfForm).toList)
//       z3.getModel(paFormula && paForm, List(equiCls))
      
    } else {
//       println
//       println("Order " + orderCount + "      " + GuessOrdering.order2string(order))
      
      // Prepare formula
      val (eqClasses, bapaSets) = createEqclasses(formula, order)
//       val numC = eqclasses.size
      
      for (eqClass <- eqClasses) {
        val allSets = bapaSets ++ eqClass.sets
        eqClass.allSets = Some(allSets.toList)
        
        val classFormula = NormalForms.nnf(renameSets(eqClass.num, allSets)(formula))
        z3.impose(classFormula)
        z3.impose(classSizeConstraints(eqClass, allSets))
      }
    }
    z3.finalCheck

      
//       val formula0 = QFBAPAtoPATranslator.rewriteSetRel(formula)
//       val (paFormula, cardSplits) = split(formula0, numC)
//
//       // Translate each class to BAPA
//       val paformBuffer = new ListBuffer[Formula]
//       paformBuffer += paFormula
//       val immutBapaSets = Set.empty ++ bapaSets
//       for ((ec@EquiClass(num, infs, sets, sups, classType, classSize), index) <- eqclasses.zipWithIndex) {
//         val allSets = immutBapaSets ++ sets
//         ec.allSets = Some(allSets.toList)
//
//         def transformTerm(term: Term): Term = term match {
//           case Op(op, terms) =>
//             Op(op, terms map transformTerm)
//           case TermVar(sym) if sym.isSet =>
//             if (allSets(sym)) TermVar(Symbol.partOf(sym, num)) else emptyset
//           case _ => term
//         }
//         val bapaBuffer = new ListBuffer[Formula]
//         for ((setExpr, nameGen) <- cardSplits)
//           bapaBuffer += transformTerm(setExpr).card === nameGen(index)
//
//         def intersection(sets: Set[Symbol]): Term = sets.toList match {
//           case Nil => fullset
//           case List(set) => Symbol.partOf(set, num)
//           case ss => Op(INTER, ss map {set => TermVar(Symbol.partOf(set, num))})
//         }
//         classType match {
//           case Singleton(false) =>
//             val infAndSupSet = intersection(infs ++ sups)
//             bapaBuffer += (fullset.card === 1)
//             if (infAndSupSet != fullset) bapaBuffer += (infAndSupSet.card === 1)
//
//           case Singleton(true) =>
//             val infSet = intersection(infs)
//             val supSet = intersection(sups)
//             bapaBuffer += (fullset.card === classSize)
//
//             assert(!infs.isEmpty && !sups.isEmpty)
//             /*if (infs == sups) {
//              bapaBuffer += (infSet.card > 0)
//              bapaBuffer += (classSize > 1) implies ((infSet ++ supSet).card > 1)
//            } else*/
//             bapaBuffer += (infSet.card > 0)
//             bapaBuffer += (supSet.card > 0)
//             bapaBuffer += (classSize > 1) implies ((infSet ++ supSet).card > 1)
//
//
//           case Bounded =>
//             val infSet = intersection(infs)
//             val supSet = intersection(sups)
//             bapaBuffer += (fullset.card === classSize)
//
//             /*if (infs == sups) {
//               if(!infs.isEmpty) bapaBuffer += ((infSet ++ supSet).card > 1)
//             } else {*/
//             if (!infs.isEmpty) bapaBuffer += (infSet.card > 0)
//             if (!sups.isEmpty) bapaBuffer += (supSet.card > 0)
//             if (!infs.isEmpty && !sups.isEmpty) bapaBuffer += ((infSet ++ supSet).card > 1)
//           // }
//           case Unbounded =>
//         }
//
//         val bapaForm = NormalForms.nnf(And(bapaBuffer.toList))
//         val (paForm, n) = QFBAPAtoPATranslator(bapaForm, num)
//         paformBuffer += paForm
//         ec.sparsenessBound = Some(n)
//       }

      // Add equality & order constraints
      /* Already added
      for (elem <- order) (elem: @unchecked) match {
        case InfElem(first :: rest) =>
          for (r <- rest) paformBuffer += (first === r)
        case SupElem(first :: rest) =>
          for (r <- rest) paformBuffer += (first === r)
        case ComboElem(first :: rest1, rest2, false) =>
          for (r <- rest1 ::: rest2) paformBuffer += (first === r)
        case ComboElem(first1 :: rest1, first2 :: rest2, true) =>
          for (r <- rest1) paformBuffer += (first1 === r)
          for (r <- rest2) paformBuffer += (first2 === r)
          paformBuffer += (first1 <= first2)
      }
      */

      // Add equality & order constraints
      /*
      for ((first :: rest) <- order; r <- rest)
        paformBuffer += (first === r)
      for (((low :: _), (high :: _)) <- order zip order.tail)
        paformBuffer += (low < high)
        */

//       val form = NormalForms.nnf(And(paformBuffer.toList))
//       z3.getModel(form, classes.toList)
  }



  private def createEqclasses(formula: Formula, order: Order) = {
    val classes = new ArrayBuffer[EquiClass]
    val sets = new MutableSet[Symbol]
    val bapaSets = new MutableSet[Symbol] ++ setvars(formula)

    var least: Bound = null
    var low: Bound = null
    order.head match {
      case SupElem(_) =>
        error("Order cannot start with only upper bounds")

      case InfElem(infs) =>
        val infSets = getInfSets(infs)
        sets ++= infSets
        low = Incl(infs)
        least = Excl(infs)

      case ComboElem(infs, sups, isLE) =>
        val infSets = getInfSets(infs)
        val supSets = getSupSets(sups)
        classes += new EquiClass(Incl(infs), Incl(sups), infSets.toList, Singleton(isLE))
        low = Excl(sups)
        sets ++= infSets
        sets --= supSets
        bapaSets --= supSets
        least = Excl(infs)
    }

    // Create merged classes
    for (elem <- order.tail) elem match {
      case SupElem(sups) =>
        val supSets = getSupSets(sups)
        classes += new EquiClass(low, Incl(sups), sets.toList, Bounded)
        sets --= supSets
        bapaSets --= supSets
        low = Excl(sups)

      case InfElem(infs) =>
        val infSets = getInfSets(infs)
        classes += new EquiClass(low, Excl(infs), sets.toList, Bounded)
        sets ++= infSets
        low = Incl(infs)

      case ComboElem(infs, sups, isLE) =>
        val infSets = getInfSets(infs)
        val supSets = getSupSets(sups)
        classes += new EquiClass(low, Excl(infs), sets.toList, Bounded)
        sets ++= infSets
        classes += new EquiClass(Incl(infs), Incl(sups), sets.toList, Singleton(isLE))
        sets --= supSets
        low = Excl(sups)
        bapaSets --= supSets
    }
    classes += new EquiClass(low, least, Nil, Unbounded)

    (classes.toSeq, bapaSets.toSet)
  }


  private def intersection(sets: Set[Symbol], classNum: Int): Term = sets.toList match {
    case Nil => null
    case List(set) => Symbol.partOf(set, classNum)
    case ss => Op(INTER, ss map {set => TermVar(Symbol.partOf(set, classNum))})
  }

  private def union(sets: Set[Symbol], classNum: Int): Term = sets.toList match {
    case Nil => emptyset
    case List(set) => Symbol.partOf(set, classNum)
    case ss => Op(UNION, ss map {set => TermVar(Symbol.partOf(set, classNum))})
  }

  private def renameSets(classNum: Int, allSets: Set[Symbol]): Formula => Formula = {
    def renameFormula(formula: Formula): Formula = formula match {
      case Not(f) => !renameFormula(f)
      case And(fs) => And(fs map renameFormula)
      case Or(fs) => Or(fs map renameFormula)
      case Predicate(cmp, ts) => Predicate(cmp, ts map renameTerm)
      case _ => formula
    }
    def renameTerm(term: Term): Term = term match {
      case TermVar(sym) if sym.isSet =>
        if (allSets(sym)) TermVar(Symbol.partOf(sym, classNum))
        else emptyset
      case Op(op, ts) => Op(op, ts map renameTerm)
      case _ => term
    }
    renameFormula _
  }

  private def classSizeConstraints(eqClass: EquiClass, allSets: Set[Symbol]) = {
    val formBuffer = new ListBuffer[Formula]

    val EquiClass(num, infs, sets, sups, classType, classSize) = eqClass

    // Size constraints
    classType match {
      case Singleton(false) =>
        val infAndSupSet = intersection(infs ++ sups, num)
        val universe = union(allSets, num)
        formBuffer += (universe.card <= 1)
        if (infAndSupSet != null) formBuffer += (infAndSupSet.card === 1)

      case Singleton(true) =>
        val infSet = intersection(infs, num)
        val supSet = intersection(sups, num)
        val universe = union(allSets, num)
        formBuffer += (universe.card <= classSize)

        assert(!infs.isEmpty && !sups.isEmpty)
        /*if (infs == sups) {
        formBuffer += (infSet.card > 0)
        formBuffer += (classSize > 1) implies ((infSet ++ supSet).card > 1)
      } else*/
        formBuffer += (infSet.card > 0)
        formBuffer += (supSet.card > 0)
        formBuffer += (classSize > 1) implies ((infSet ++ supSet).card > 1)


      case Bounded =>
        val infSet = intersection(infs, num)
        val supSet = intersection(sups, num)
        val universe = union(allSets, num)
        formBuffer += (universe.card <= classSize)

        /*if (infs == sups) {
          if(!infs.isEmpty) formBuffer += ((infSet ++ supSet).card > 1)
        } else {*/
        if (!infs.isEmpty) formBuffer += (infSet.card > 0)
        if (!sups.isEmpty) formBuffer += (supSet.card > 0)
        if (!infs.isEmpty && !sups.isEmpty) formBuffer += ((infSet ++ supSet).card > 1)
      // }
      case Unbounded =>
    }
    And(formBuffer.toList)
  }



}
