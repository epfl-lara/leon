package leon
package synthesis.disambiguation

import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types.{TypeTree, TupleType, BooleanType}
import purescala.Common.{Identifier, FreshIdentifier}
import purescala.Definitions.{FunDef, Program, TypedFunDef, ValDef}
import purescala.DefOps
import scala.collection.mutable.ListBuffer
import leon.LeonContext
import leon.purescala.Definitions.TypedFunDef
import leon.verification.VerificationContext
import leon.verification.VerificationPhase
import leon.solvers._
import scala.concurrent.duration._
import leon.verification.VCStatus
import leon.verification.VCResult
import leon.evaluators.AbstractEvaluator
import leon.evaluators.DefaultEvaluator

object InputRecCoverage {
  class W(val e: Expr) {
    def somewhere(f: Expr): Boolean = e eq f
    // To ensure that the "equals" method of exprs is not used during the computation.
  }
}

class InputRecCoverage(fd: FunDef, fds: Set[FunDef])(implicit ctx: LeonContext, program: Program) {
  import InputRecCoverage._
  val inputCoverage = new InputCoverage(fd, fds)
  
  
  
  /** Returns a stream of rec-covering inputs for the function `f` to cover all functions in `{ f } U fds`.
    *  
    *  This means that for each concatenation operation, there is an input example which can differentiate between this concatenation and the inverse concatenation.
    **/
  def result(): Stream[Seq[Expr]] = {
    var identifiableInputs = Map[Seq[Expr], Seq[Expr]]()
    var inputs = inputCoverage.recordMapping().result().map{input => 
      val res = input.map(QuestionBuilder.makeGenericValuesUnique)
      identifiableInputs += input -> res
      res
    }
    
    def collectConcatenations(e: Expr) = ExprOps.collect{ case s: StringConcat => Set(new W(s)) case _ => Set[W]() }(e)
    
    val concatenations = collectConcatenations(fd.body.get) ++ fds.flatMap { fd => collectConcatenations(fd.body.get) }
    
    // For each of these concatenations, we check that there is at least one input which if evaluated while it is reverse, the result would be different.
    // If not, we expand the covering example.
    
    val originalEvaluator = new DefaultEvaluator(ctx, program)
    val originalOutputs: Map[Seq[Expr], Expr] = inputs.map(input => input -> originalEvaluator.eval(functionInvocation(fd, input)).result.get).toMap
    for(stringConcatW <- concatenations; stringConcat = stringConcatW.e) {
      val stringConcatReversed = stringConcat match {
        case StringConcat(a, b) => StringConcat(b, a).copiedFrom(stringConcat)
      }
      
      val (permuttedProgram, idMap, fdMap, cdMap) = DefOps.replaceFunDefs(program)({
        (f: FunDef) =>
          if(ExprOps.exists(stringConcat == _)(fd.body.get)) {
            val new_f = f.duplicate()
            new_f.body = f.body.map(body => ExprOps.preMap(e => if(stringConcat eq e) Some(stringConcatReversed) else None)(body))
            Some(new_f)
          } else None
      })
      
      val modifiedEvaluator = new DefaultEvaluator(ctx, permuttedProgram)
      
      val oneInputMakesItDifferent = inputs.exists(input => 
        modifiedEvaluator.eval(functionInvocation(fdMap(fd), input)).result.get != originalOutputs(input))
      
      if(!oneInputMakesItDifferent) {
        // Now we need to find an input which makes a difference if possible.
        println("No input make this concatenation differ in output when permutted: " + stringConcat + " -> " + stringConcatReversed)
        // First, make all its terminals (strings and numbers) unique.
        val covering = inputCoverage.getRecordMapping()
        println(s"Input that can cover $stringConcat are " + covering.getOrDefault(stringConcat, Set()).map(x => identifiableInputs.getOrElse(x, x)).mkString(", "))
        
        
      } // Else that's fine, the example covers the case.
    }
    
    inputs
  }
}