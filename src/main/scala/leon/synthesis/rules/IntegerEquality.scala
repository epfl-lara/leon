/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package synthesis
package rules


import scala.annotation.tailrec
import scala.collection.mutable.ListBuffer
import evaluators.AbstractEvaluator
import purescala.Definitions._
import purescala.Common._
import purescala.Types._
import purescala.Constructors._
import purescala.Expressions._
import purescala.Extractors._
import purescala.TypeOps
import purescala.DefOps
import purescala.ExprOps
import purescala.SelfPrettyPrinter
import solvers.ModelBuilder
import solvers.string.StringSolver
import programsets.DirectProgramSet
import programsets.JoinProgramSet
import leon.synthesis.comfusy._
import leon.utils.Bijection

class VarContext(val inputVariables: Set[Identifier], val outputVariables: Set[Identifier], val sctx: SearchContext) {
  private var idToInputVar = new Bijection[Identifier, InputVar]
  private var idToOutputVar = new Bijection[Identifier, OutputVar]
  
  def getInputVar(id: Identifier): InputVar = {
    idToInputVar.cachedB(id){
      var i = 0
      while(idToInputVar.containsB(InputVar(id.name + i))) i+=1
      InputVar(id.name + i)
    }
  }
  
  def getOutputVar(id: Identifier): OutputVar = {
    idToOutputVar.cachedB(id){
      var i = 0
      while(idToOutputVar.containsB(OutputVar(id.name + i))) i+=1
      OutputVar(id.name + i)
    }
  }
  
  def getIdentifier(iv: InputVar): Identifier= {
    idToInputVar.cachedA(iv){
      FreshIdentifier(iv.name, IntegerType, false)
    }
  }
  
  def getIdentifier(ov: OutputVar): Identifier= {
    idToOutputVar.cachedA(ov){
      FreshIdentifier(ov.name, IntegerType, false)
    }
  }
}

case class NotInputVarException(msg: String) extends Exception(msg)

object ComfusyConverters {
  
  def convertToAPAInputTerm(e: Expr)(implicit vc: VarContext): APAInputTerm = e match {
    case Plus(a, b) => convertToAPAInputTerm(a) + convertToAPAInputTerm(b)
    case Minus(a, b) => convertToAPAInputTerm(a) - convertToAPAInputTerm(b)
    case UMinus(a) => -convertToAPAInputTerm(a)
    case Times(a, b) => convertToAPAInputTerm(a) * convertToAPAInputTerm(b)
    case Division(a, b) => convertToAPAInputTerm(a) / convertToAPAInputTerm(b)
    case IfExpr(LessEquals(a1, InfiniteIntegerLiteral(zero)), UMinus(a2), a3) if a1 == a2 && a2 == a3 && zero == BigInt(0) => APAInputAbs(convertToAPAInputTerm(a1))
    //APAInputMod is not supported in Comfusy
    case Variable(i) if vc.inputVariables contains i => APAInputCombination(0, (1, vc.getInputVar(i))::Nil)
    case InfiniteIntegerLiteral(k) => APAInputCombination(k.toInt, Nil)
    case _ => throw NotInputVarException(s"$e is not an input variable. Only + / * - and ${vc.inputVariables.mkString(",")} are allowed")
  }
  
  def convertToAPACombination(e: Expr)(implicit vc: VarContext): APACombination = e match {
    case Plus(a, b) =>  convertToAPACombination(a) + convertToAPACombination(b)
    case Minus(a, b) => convertToAPACombination(a) - convertToAPACombination(b)
    case UMinus(a) => -convertToAPACombination(a)
    case Times(a, b) => 
      if(isInputVarParsable(a)) {
        convertToAPAInputTerm(a) * convertToAPACombination(b)
      } else {
        convertToAPAInputTerm(b) * convertToAPACombination(a)
      }
    case Division(a, b) => 
       convertToAPACombination(a) / convertToAPAInputTerm(b)
    case Variable(i) if vc.outputVariables contains i =>
      APACombination(APAInputCombination(0), (APAInputCombination(1), vc.getOutputVar(i))::Nil)
    case e => APACombination(convertToAPAInputTerm(e), Nil)
  }
  def convertToAPAEqualZero(e: Equals)(implicit vc: VarContext) = {
    APAEqualZero(convertToAPACombination(e.lhs) - convertToAPACombination(e.rhs))
  }
  
  def isInputVarParsable(e: Expr)(implicit vc: VarContext): Boolean = {
    def aux(e: Expr): Boolean = e match {
      case Plus(a, b) => aux(a) && aux(b)
      case Minus(a, b) => aux(a) && aux(b)
      case UMinus(a) => aux(a)
      case Times(a, b) => aux(a) && aux(b)
      case Division(a, b) => aux(a) && aux(b)
      //case Remainder(a, b) => aux(a) && aux(b)
      //case Modulo(a, b) => aux(a) && aux(b)
      case Variable(i) => vc.inputVariables contains i
      case InfiniteIntegerLiteral(k) => true
      case _ => false
    }
    aux(e)
  }
  
  def isLinInOutputVariables(e: Expr)(implicit vc: VarContext): Boolean = {
    def aux(e: Expr): Boolean = e match {
      case Plus(a, b) =>  aux(a) && aux(b)
      case Minus(a, b) => aux(a) && aux(b)
      case UMinus(a) => aux(a)
      case Times(a, b) => (isInputVarParsable(a) && isLinInOutputVariables(b)) ||
                          (isInputVarParsable(b) && isLinInOutputVariables(a))
      case Division(a, b) => isInputVarParsable(b) && isLinInOutputVariables(a)
      case Variable(i) => (vc.inputVariables contains i) || (vc.outputVariables contains i)
      case InfiniteIntegerLiteral(k) => true
      case _ => isInputVarParsable(e)
    }
    aux(e)
  }
  
  def isLinEqInOutputVariables(e: Expr)(implicit vc: VarContext): Boolean = {
    e match {
      case Equals(a, b) =>  isLinInOutputVariables(a) &&
                            isLinInOutputVariables(b)
    }
  }
  
  
  
  def convertToSolution(cond: APACondition, prog: APAProgram)(implicit vc: VarContext): Solution = {
    val precond: Expr = APAConditionToExpr(cond)
    val term: Expr = APAProgramToExpr(prog, prog.output_variables)
    Solution(precond, Set.empty, term)
  }
  
  def APACombinationToExpr(e: APACombination)(implicit vc: VarContext): Expr = e match {
    case APACombination(coef, varsWithCoefs) => (APAInputTermToExpr(coef) /: varsWithCoefs) { (c: Expr, iv) =>
      val (i, v) = iv
      Plus(c, Times(APAInputTermToExpr(i), Variable(vc.getIdentifier(v))))
    }
  }
  
  def APAFormulaToExpr(e: APAFormula)(implicit vc: VarContext): Expr = e match {
    case e: APAEquation => APAEquationToExpr(e)
    case APAConjunction(conjuncts) => And(conjuncts map APAFormulaToExpr)
    case APADisjunction(conjuncts) => Or(conjuncts map APAFormulaToExpr)
    case APANegation(formula) => Not(APAFormulaToExpr(formula))
  }
  
  def APAEquationToExpr(e: APAEquation)(implicit vc: VarContext): Expr = e match {
    case APADivides(coefficient, pac) => Equals(Modulo(APACombinationToExpr(pac), APAInputTermToExpr(coefficient)), InfiniteIntegerLiteral(BigInt(0)))
    case APAEqualZero(pac) => Equals(APACombinationToExpr(pac), InfiniteIntegerLiteral(BigInt(0)))
    case APAGreaterZero(pac) => GreaterThan(APACombinationToExpr(pac), InfiniteIntegerLiteral(BigInt(0)))
    case APAGreaterEqZero(pac) => GreaterEquals(APACombinationToExpr(pac), InfiniteIntegerLiteral(BigInt(0)))
    case APATrue() => BooleanLiteral(true)
    case APAFalse() => BooleanLiteral(false)
  }
  
  def InputAssignmentToExpr(input_assignment: InputAssignment)(implicit vc: VarContext): Expr => Expr =  {
    input_assignment match {
      case SingleInputAssignment(iv, t) =>
        (x: Expr) => Let(vc.getIdentifier(iv), APAInputTermToExpr(t), x)
      case BezoutInputAssignment(vs, ts) =>
        val tsConverted = ts map APAInputTermToExpr
        import vc.sctx.program.library.{ List => LeonList, Cons => LeonCons, Nil => LeonNil }
        val listType = LeonList.get
        val applyfun = vc.sctx.program.library.lookupUnique[FunDef]("leon.collection.List.apply")
        val bezoutWithBase = vc.sctx.program.library.bezoutWithBase.get
        val b = FreshIdentifier("b", listType.typed(Seq(listType.typed(Seq(IntegerType)))), false)
        val decomposed: List[Expr => Expr] = vs.zipWithIndex.map{ case (lv, i) =>
          lv.zipWithIndex.map { case (v, j) =>
            (w: Expr) =>
              Let(vc.getIdentifier(v),
                  functionInvocation(applyfun, Seq(
                      functionInvocation(applyfun, Seq(Variable(b), InfiniteIntegerLiteral(BigInt(i)))),
                          InfiniteIntegerLiteral(BigInt(j)))), w)
          }
        }.flatten
        val decomposed_recomposed = decomposed.reduce(_ compose _)
        val tsConvertedToList = (tsConverted :\ (CaseClass(CaseClassType(LeonNil.get, Seq(IntegerType)), Seq()): Expr)) {
          (v, l) =>
            CaseClass(CaseClassType(LeonCons.get, Seq(IntegerType)), Seq(v, l))
        }
        val initial_fun = (x: Expr) => Let(b, functionInvocation(bezoutWithBase, Seq(InfiniteIntegerLiteral(BigInt(1)), tsConvertedToList)), x)
        decomposed_recomposed compose initial_fun
    }
  }
  
  def APASplitConditionToExpr(sc: APASplitCondition)(implicit vc: VarContext): Expr = sc match {
    case APAEmptySplitCondition() => BooleanLiteral(true)
    case APACaseSplitCondition(csl) => Or(csl.map(e => APAAbstractConditionToExpr(e)))
    case APAForCondition(vl, lower_range, upper_range, global_condition) =>
      val range = vc.sctx.program.library.lookupUnique[FunDef]("leon.collection.List.range")
      val flatMap = vc.sctx.program.library.lookupUnique[FunDef]("leon.collection.List.flatMap")
      val map = vc.sctx.program.library.lookupUnique[FunDef]("leon.collection.List.map")
      val exists = vc.sctx.program.library.lookupUnique[FunDef]("leon.collection.List.exists")
      val basic_range = functionInvocation(range, Seq(APAInputTermToExpr(lower_range), APAInputTermToExpr(upper_range)))
      var ranges = basic_range
      var tupleType: TypeTree = IntegerType
      vl.tail foreach { k =>
        val t = FreshIdentifier("t", IntegerType)
        val i = FreshIdentifier("i", IntegerType)
        ranges = functionInvocation(flatMap, Seq(ranges, Lambda(Seq(ValDef(t)),
            functionInvocation(map, Seq(basic_range, Lambda(Seq(ValDef(i)), tupleWrap(Seq(Variable(i), Variable(t)))))))))
        tupleType = TupleType(Seq(IntegerType, tupleType))
      }
      def getPattern(i: InputVar): Pattern = WildcardPattern(Some(vc.getIdentifier(i)))
      val tuplePattern = (vl.init :\ getPattern(vl.last)) {
        case (v, p) => tuplePatternWrap(Seq(getPattern(v), p))
      }
      
      val evars = FreshIdentifier("evars", tupleType)
      functionInvocation(exists, Seq(ranges, 
        Lambda(Seq(ValDef(evars)),
            MatchExpr(Variable(evars),
                Seq(MatchCase(tuplePattern, None, APAConditionToExpr(global_condition)))))
      ))
  }
  
  def APAAbstractConditionToExpr(cond: APAAbstractCondition)(implicit vc: VarContext): Expr = {
    cond match {
      case c: APACondition => APAConditionToExpr(c)
      case s: APASplitCondition => APASplitConditionToExpr(s)
    }
  }
  
  def ListOutputAssignmentToExpr(l: List[(OutputVar, APATerm)])(implicit vc: VarContext): Expr => Expr = {
    val outputAssignments = if(l.isEmpty) None
      else Some((l map (e => (x: Expr) => Let(vc.getIdentifier(e._1), APATermToExpr(e._2), x))) reduce (_ compose _))
    (e: Expr) => outputAssignments.map(f => f(e)).getOrElse(e)
  }
  
  def ListInputAssignmentToExpr(l: List[InputAssignment])(implicit vc: VarContext): Expr => Expr = {
    val inputAssignments = if(l.isEmpty) None
      else Some((l map (e => InputAssignmentToExpr(e))) reduce (_ compose _))
    (e: Expr) => inputAssignments.map(f => f(e)).getOrElse(e)
  }

  def APAConditionToExpr(cond: APACondition)(implicit vc: VarContext): Expr = {
    val assigns = ListInputAssignmentToExpr(cond.input_assignment)
    val g = APAFormulaToExpr(cond.global_condition)
    if(cond.isTrivial) {
      BooleanLiteral(true)
    } else {
      cond.pf match {
       case APAEmptySplitCondition() =>
         assigns(g)
       case _ => // There are some more splits.
         if(g == BooleanLiteral(true)) {
           assigns(APASplitConditionToExpr(cond.pf))
         } else {
           assigns(And(g, APASplitConditionToExpr(cond.pf)))
         }
      }
    }
  }

  def APAProgramToExpr(prog: APAProgram, expected_output_vars: List[OutputVar])(implicit vc: VarContext): Expr = {
    val assigns = ListInputAssignmentToExpr(prog.input_assignment)
    val affectedOutputVariables = prog.output_assignment.map(_._1).toSet
    val referedOutputVariables = prog.output_assignment.flatMap(_._2.output_variables) filterNot affectedOutputVariables
    val assignMiddle = APASplitToExpr(prog.case_splits, referedOutputVariables)
    val assigns2 = ListOutputAssignmentToExpr(prog.output_assignment)
    val output_expr = tupleWrap(expected_output_vars.map(ov => Variable(vc.getIdentifier(ov))))
    assigns(assignMiddle(assigns2(output_expr)))
  }
  
  def conditionProgramToIfExpr(p: (APACondition, APAProgram), expected_output: List[OutputVar])(implicit vc: VarContext): Expr => Expr = {
    val subprogram = APAProgramToExpr(p._2, expected_output)
    (els: Expr) => IfExpr(APAConditionToExpr(p._1), subprogram, els)
  }
  
  def APASplitToExpr(p: APASplit, expected_output: List[OutputVar])(implicit vc: VarContext): Expr => Expr = p match {
    case APAFalseSplit() => Let(FreshIdentifier("wrong", UnitType), NoTree(tupleTypeWrap(expected_output.map(_ => IntegerType))), _)
    case APAEmptySplit() => e => e
    case APACaseSplit(conditionPrograms) =>
      val cps = conditionPrograms map (cp => conditionProgramToIfExpr(cp, expected_output))
      if(cps.isEmpty) e => e
      else {
        val composition = cps.reduce(_ compose _)
        (x: Expr) => letTuple(expected_output.map(vc.getIdentifier),
            composition(Error(tupleTypeWrap(expected_output.map((ov: OutputVar) => IntegerType)), "Unreachable case")), x)
      }
    case APAForSplit(vl: List[InputVar], lower_range: APAInputTerm, upper_range: APAInputTerm, condition: APACondition, program: APAProgram) =>
      import vc.sctx.program.library.{None => LeonNone, Some => LeonSome, List => LeonList, Cons => LeonCons, Nil => LeonNil, _}
      val range =   lookupUnique[FunDef]("leon.collection.List.range")
      val flatMap = lookupUnique[FunDef]("leon.collection.List.flatMap")
      val map =     lookupUnique[FunDef]("leon.collection.List.map")
      val find =  lookupUnique[FunDef]("leon.collection.List.find")
      val get =  lookupUnique[FunDef]("leon.collection.Option.get")
      val basic_range = functionInvocation(range, Seq(APAInputTermToExpr(lower_range), APAInputTermToExpr(upper_range)))
      var ranges = basic_range
      var tupleType: TypeTree = IntegerType
      vl.tail foreach { k =>
        val t = FreshIdentifier("t", IntegerType)
        val i = FreshIdentifier("i", IntegerType)
        ranges = functionInvocation(flatMap, Seq(ranges, Lambda(Seq(ValDef(t)),
            functionInvocation(map, Seq(basic_range, Lambda(Seq(ValDef(i)), tupleWrap(Seq(Variable(i), Variable(t)))))))))
        tupleType = TupleType(Seq(IntegerType, tupleType))
      }
      def getPattern(i: InputVar): Pattern = WildcardPattern(scala.Some(vc.getIdentifier(i)))
      val tuplePattern = (vl.init :\ getPattern(vl.last)) {
        case (v, p) => tuplePatternWrap(Seq(getPattern(v), p))
      }
      
      val evars = FreshIdentifier("evars", tupleType)
      val findExpr = functionInvocation(find, Seq(ranges, 
        Lambda(Seq(ValDef(evars)),
            MatchExpr(Variable(evars),
                Seq(MatchCase(tuplePattern, scala.None, APAConditionToExpr(condition)))))
      ))
      val finalExpr = functionInvocation(get, Seq(findExpr))
      (x: Expr) => letTuple(expected_output.map(vc.getIdentifier), finalExpr, x)
  }
  
  def APATermToExpr(e: APATerm)(implicit vc: VarContext): Expr = e match {
    case APADivision(n, d) => Division(APACombinationToExpr(n), APAInputTermToExpr(d))
    case APAMinimum(l) => l match {
      case Nil => throw new Exception("Minimum of nothing")
      case a::Nil => APATermToExpr(a)
      case l =>
        val minDef = vc.sctx.program.library.lookup("leon.math.min").collect{
          case fd: FunDef => fd
        }.filter { fd => fd.paramIds.head.getType == IntegerType }.head
        
        (l.init :\ APATermToExpr(l.last)) { (v, res) =>
          functionInvocation(minDef, Seq(APATermToExpr(v), res))
        }
    }
    case APAMaximum(l) => l match {
      case Nil => throw new Exception("Maximum of nothing")
      case a::Nil => APATermToExpr(a)
      case l =>
        val maxDef = vc.sctx.program.library.lookup("leon.math.max").collect{
          case fd: FunDef => fd
        }.filter { fd => fd.paramIds.head.getType == IntegerType }.head
        
        (l.init :\ APATermToExpr(l.last)) { (v, res) =>
          functionInvocation(maxDef, Seq(APATermToExpr(v), res))
        }
    }
    case a: APACombination =>
      APACombinationToExpr(a)
  }
  def APAInputTermToExpr(t: APAInputTerm)(implicit vc: VarContext): Expr = t match {
    case APAInputCombination(coef, input_linear) =>
      ((InfiniteIntegerLiteral(BigInt(coef)): Expr) /: input_linear) { (c: Expr, iv) =>
        val (i, v) = iv
        Plus(c, Times(InfiniteIntegerLiteral(i), Variable(vc.getIdentifier(v))))
      }
    case APAInputDivision(numerator, denominator) =>
      Division(APAInputTermToExpr(APAInputMultiplication(numerator)), APAInputTermToExpr(APAInputMultiplication(denominator)))
    case APAInputMultiplication(operands) =>
      val v = (operands map APAInputTermToExpr)
      v match {
        case Nil => InfiniteIntegerLiteral(1)
        case a::Nil => a
        case l => l.reduce(Times)
      }
    case APAInputAddition(operands) =>
      val v = (operands map APAInputTermToExpr)
      v match {
        case Nil => InfiniteIntegerLiteral(0)
        case a::Nil => a
        case l => l.reduce(Plus)
      }
    case APAInputAbs(a) =>
      val absFun = vc.sctx.program.library.lookupUnique[FunDef]("leon.math.abs")
      functionInvocation(absFun, Seq(APAInputTermToExpr(a)))
    case APAInputGCD(numbers) =>
      import vc.sctx.program.library._
      val gcdFun = lookupUnique[FunDef]("leon.math.gcdlist")
      val args = numbers map APAInputTermToExpr
      val l = (args :\ (CaseClass(CaseClassType(Nil.get, Seq(IntegerType)), Seq()): Expr)) { (v, l) =>
        CaseClass(CaseClassType(Cons.get, Seq(IntegerType)), Seq(v, l))
      }
      functionInvocation(gcdFun, Seq(l))
    case APAInputLCM(numbers) =>
      import vc.sctx.program.library._
      val lcmFun = lookupUnique[FunDef]("leon.math.lcmlist")
      val args = numbers map APAInputTermToExpr
      val l = (args :\ (CaseClass(CaseClassType(Nil.get, Seq(IntegerType)), Seq()): Expr)) { (v, l) =>
        CaseClass(CaseClassType(Cons.get, Seq(IntegerType)), Seq(v, l))
      }
      functionInvocation(lcmFun, Seq(l))
  }
}

case object IntegerEquality extends Rule("Solve integer equality"){
  
  import ComfusyConverters._
  
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    implicit lazy val vc = new VarContext(p.as.toSet, p.xs.toSet, hctx)
    p.phi match {
      case TopLevelAnds(conjuncts) =>
        val candidates: List[Equals] = conjuncts.toList collect { case e: Equals => e } filter { e => isLinEqInOutputVariables(e) }
        if(candidates.isEmpty) {
          Nil
        } else {
          val realCandidates  = candidates map (e => convertToAPAEqualZero(e)) sortWith APASynthesis.by_least_outputvar_coef
          val problem = new APASynthesis(FormulaSplit(realCandidates, Nil, Stream.empty), p.as.toList.map(vc.getInputVar), p.xs.toList.map(vc.getOutputVar))
          List(RuleInstantiation("Solve integer equalities") {
            val (cond, prog) = problem.solve()
            val solution = convertToSolution(cond, prog)
            RuleClosed(solution)
          })
        }
      case _ => Nil
    }
  }
}