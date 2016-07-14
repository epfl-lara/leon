package leon
package synthesis
package disambiguation

import leon.LeonContext
import leon.evaluators.DefaultEvaluator
import leon.evaluators.DefaultRecContext
import purescala.Common.{Identifier, FreshIdentifier}
import purescala.Constructors._
import purescala.DefOps
import purescala.Definitions.FunDef
import purescala.Definitions.Program
import purescala.ExprOps
import purescala.Definitions.{CaseClassDef, _}
import purescala.Expressions._
import purescala.Extractors._
import purescala.Types._
import purescala.TypeOps
import leon.datagen.GrammarDataGen
import leon.grammars.ValueGrammar
import leon.purescala.TypeOps
import leon.evaluators.AbstractEvaluator
import leon.purescala.TypeOps
import scala.collection.mutable.Queue
import java.util.IdentityHashMap

object InputRecCoverage {
  class W[T <: Expr](val e: T) {
    def somewhere(f: Expr): Boolean = e eq f
    // To ensure that the "equals" method of exprs is not used during the computation.
  }
  
  /** Returns true if the expression contains strings or integers */
  def isMarkedWithStringOrInt(e: Expr) =
     ExprOps.exists{
      case StringLiteral(_) => true
      case InfiniteIntegerLiteral(_) => true
      case IntLiteral(_) => true
      case _ => false
    }(e)
}

class InputRecCoverage(fd: FunDef, fds: Set[FunDef])(implicit ctx: LeonContext, program: Program) {
  import InputRecCoverage._
  val inputCoverage = new InputCoverage(fd, fds)
  
  /** Flattens a string concatenation into a list of expressions */
  def flatten(s: StringConcat): List[Expr] = s match {
    case StringConcat(a: StringConcat, b: StringConcat) => flatten(a) ++ flatten(b)
    case StringConcat(a, b: StringConcat) => a :: flatten(b)
    case StringConcat(a: StringConcat, b) => flatten(a) ++ List(b)
    case StringConcat(a, b) => List(a, b)
  }
  
  /** Creates a string concatenation from a list of expression. The list should have size >= 2.*/
  def rebuild(e: List[Expr]): StringConcat = e match {
    case List(a, b) => StringConcat(a, b)
    case a::l => StringConcat(a, rebuild(l))
    case _ => throw new Exception("List with less than 2 elements?!")
  }
  
  /** Flattens a string concatenation into a list of expressions */
  def permutations(s: StringConcat): Stream[StringConcat] = {
    flatten(s).permutations.toStream.tail.map(x => rebuild(x).copiedFrom(s))
  }
  
  def allConcatenations(): Set[W[StringConcat]] = {
    var concatenations = Set[W[StringConcat]]()
    
    def collectConcatenations(e: Expr, keepConcatenations: Boolean = true): Unit = e match {
      case s@StringConcat(a, b) => if(keepConcatenations) concatenations += new W(s) // Stop at the first concatenation.
        collectConcatenations(a, false)
        collectConcatenations(b, false)
      case Operator(es, builder) => for(e <- es)
        collectConcatenations(e, true)
    }
    
    collectConcatenations(fd.body.get)
    for(fd <- fds) {
      collectConcatenations(fd.body.get)
    }
    concatenations
  }
  
  /** Assert function for testing if .result() is rec-covering. */
  def assertIsRecCovering(inputs: Stream[Seq[Expr]]): Unit = {
    // Contains the set of top-level concatenations in all programs.
    val concatenations = allConcatenations()
    
    // For each of these concatenations, we check that there is at least one input which if evaluated while it is reverse, the result would be different.
    // If not, we expand the covering example.
    
    val originalEvaluator = new DefaultEvaluator(ctx, program)
    val originalOutputs: Map[Seq[Expr], Expr] = inputs.map(input => input -> originalEvaluator.eval(functionInvocation(fd, input)).result.get).toMap
    for(stringConcatW <- concatenations; stringConcat = stringConcatW.e; stringConcatReversed <- permutations(stringConcat)) {

      val transformer = DefOps.funDefReplacer {
        (f: FunDef) =>
          if(f.body.exists(body => ExprOps.exists(stringConcat eq _)(body))) {
            val new_f = f.duplicate()
            new_f.body = f.body.map(body => ExprOps.preMap(e => if(stringConcat eq e) { Some(stringConcatReversed)} else None)(body))
            Some(new_f)
          } else None
      }
      val permuttedProgram = DefOps.transformProgram(transformer, program)
      val modifiedEvaluator = new DefaultEvaluator(ctx, permuttedProgram)
      
      val oneInputMakesItDifferent = inputs.exists(input => 
        modifiedEvaluator.eval(functionInvocation(transformer.transform(fd), input)).result.get != originalOutputs(input))
      
      assert(oneInputMakesItDifferent, "No input made the change " + stringConcat + " -> " + stringConcatReversed + " produce a different result")
    }
  }
  
  /** Returns a stream of rec-covering inputs for the function `f` to cover all functions in `{ f } U fds`.
    *  
    * This means that for each concatenation operation, there is an input example which can differentiate between this concatenation and any of its permutations if possible.
    **/
  def result(): Stream[Seq[Expr]] = {
    var identifiableInputs = Map[Seq[Expr], Seq[Expr]]()
    var inputs = inputCoverage.recordMapping().result().map{input => 
      val res = input.map(QuestionBuilder.makeGenericValuesUnique)
      identifiableInputs += input -> res
      res
    }
    
    // Contains the set of top-level concatenations in all programs.
    val concatenations = allConcatenations()
    
    // For each of these concatenations, we check that there is at least one input which if evaluated while it is reverse, the result would be different.
    // If not, we expand the covering example.
    
    val originalEvaluator = new DefaultEvaluator(ctx, program)
    var originalOutputs: Map[Seq[Expr], Expr] = inputs.map(input => input -> originalEvaluator.eval(functionInvocation(fd, input)).result.get).toMap
    for(stringConcatW <- concatenations; stringConcat = stringConcatW.e; stringConcatReversed <- permutations(stringConcat)) {
      //val (permuttedProgram, idMap, fdMap, cdMap) = DefOps.replaceFunDefs(program)({
      val transformer = DefOps.funDefReplacer {
        (f: FunDef) =>
          if(f.body.exists(body => ExprOps.exists(stringConcat eq _)(body))) {
            val new_f = f.duplicate()
            new_f.body = f.body.map(body => ExprOps.preMap(e => if(stringConcat eq e) { Some(stringConcatReversed)} else None)(body))
            Some(new_f)
          } else None
      }
      val permuttedProgram = DefOps.transformProgram(transformer, program)
      val modifiedEvaluator = new DefaultEvaluator(ctx, permuttedProgram)
      
      val oneInputMakesItDifferent = inputs.exists(input => 
        modifiedEvaluator.eval(functionInvocation(transformer.transform(fd), input)).result.get != originalOutputs(input))
      
      if(!oneInputMakesItDifferent) {
        // Now we need to find an input which makes a difference if possible, when modified.
        println("No input make this concatenation differ in output when permutted: " + stringConcat + " -> " + stringConcatReversed)
        println("    mappings:\n" + inputs.map(input => input + "->" + originalEvaluator.eval(functionInvocation(fd, input)).result.get).mkString("\n"))
        println("New mappings:\n" + inputs.map(input => input + "->" + modifiedEvaluator.eval(functionInvocation(transformer.transform(fd), input)).result.get).mkString("\n"))
        // First, make all its terminals (strings and numbers) unique.
        val covering = inputCoverage.getRecordMapping()
        val coveringInputs = Option(covering.get(stringConcat)).getOrElse(Set()).map(x => identifiableInputs.getOrElse(x, x))
        //println(s"Input that can cover $stringConcat are " + coveringInputs.mkString(", "))
        
        val input = coveringInputs.head
        var mappingAtStringConcatOpt: Option[AbstractEvaluator#RC] = None
        val please = new AbstractEvaluator(ctx, program) {
          override def e(expr: Expr)(implicit rctx: RC, gctx: GC) = {
            if(expr eq stringConcat) {
              //println(s"Found string concat $stringConcat. Mapping = " + rctx)
              rctx.mappings.values.find{v =>
                  !input.exists(i => ExprOps.exists{ case e if e eq v => true case _ => false}(i))
              } match {
                case None =>
                case Some(v) =>
                  throw new Exception(s"Value not present from input ($input): $v")
                }
              mappingAtStringConcatOpt = Some(rctx)
            }
            super.e(expr)
          }
        }
        please eval functionInvocation(fd, input)
        
        // Now we now for each term of the stringConcat which is the sub-expression of the input which is used for computation,
        // and we can replace it if
        // 1) The function call is more general, => we make sure to insert a string or number which make it identifiable
        // 2) If not possible, the function call is more general, but inserting strings or numbers is not feasible.
        // 3) The function call can handle only finitely number of values => We duplicate the input to cover all these possible values.
        
        val mappingAtStringConcat = mappingAtStringConcatOpt.getOrElse(throw new Exception(s"Did not find an execution context for $stringConcat when evaluating $input"))
        
        val members = flatten(stringConcat)
        println(s"For the input $input and concatenation $stringConcat")
        var newInput = Seq(input)
        val toReplace = new IdentityHashMap[Expr, List[Expr]]()
        for(m <- members) {
          m match {
            case FunctionInvocation(TypedFunDef(fd, targs), Seq(Variable(id))) =>
              mappingAtStringConcat.mappings.get(id) match {
                case Some(expr) =>
                  //println(s"Mapping $m is computed on $expr (with formula ${mappingAtStringConcat.mappingsAbstract(id)})")
                  // expr is a sub-expression of input.
                  // fd is the function called with the argument expr.
                  if(!isMarkedWithStringOrInt(expr)) {
                    val mainArg = fd.paramIds(0)
                    markWithStringOrInt(mainArg.getType, tupleWrap(input)) match { // TODO: Enumerate all possible values if not markable.
                      case Some(expr_marked) =>
                        println(s"Expr unisized: $expr_marked")
                        if(!input.exists(i => ExprOps.exists{ case e if e eq expr => true case _ => false}(i))) {
                          throw new Exception(s"Did not find $expr (${expr.##}) in $input")
                        }
                        toReplace.put(expr, List(expr_marked))
                      case None =>
                        println("Not possible to mark the string, reverting to enumeration strategies")
                        // If there is a finite number of values at some place, replace with each of them.
                        val exprs = if(TypeOps.typeCardinality(mainArg.getType).nonEmpty) {
                          println("Finite enumeration")
                          all(mainArg.getType).toList
                        } else {
                          println("Infinite enumeration. Taking 5 values")
                          // Else try to find other values which make them identifiable at some point.
                          all(mainArg.getType).take(5).toList
                        }
                        println(s"$expr -> $exprs")
                        toReplace.put(expr, exprs)
                    }
                  } // Else nothing to do, there is already a unique identifier to expr.
                  
                case None => throw new Exception(s"No binding at evaluation time for $id ... something is wrong.")
              }
            case IntegerToString(Variable(id)) => // Nothing to do, already identified
            case Int32ToString(Variable(id)) => // Nothing to do, already identified
            case BooleanToString(Variable(id)) => // TODO: Enumerate all possible values
            case CharToString(Variable(id)) => // Nothing to do, already identified
            case Variable(id) => // TODO: Enumerate all possible values of this id or have an identifiable one ?
            case StringLiteral(k) => // Nothing to do, already identified
            case e => throw new Exception(s"Rec-coverage is not supported when concatenating something else than fun(id) and constants; got $m")
          }
        }
        if(!toReplace.isEmpty()) {
          val new_inputs: Seq[Seq[Expr]] =
            leon.utils.SeqUtils.cartesianProduct(input.map(i => ExprOps.postFlatmap{ case e if toReplace.containsKey(e) => Some(toReplace.get(e)) case _ => None}(i)))
          println(s"Added new input: ${new_inputs.mkString("\n")}")
          for(new_input <- new_inputs) {
            originalOutputs += new_input -> originalEvaluator.eval(functionInvocation(fd, new_input)).result.get
            newInput = newInput :+ new_input
          }
          inputs = inputs.flatMap{ i => if(i == input) new_inputs else Some(input) }.distinct
          println(s"inputs: ${inputs.mkString("\n")}")
        } else {
          println(s"Did not find anything to identify the expr $stringConcat")
        }
        // Now we find which arguments are given to the function 
        
      } // Else that's fine, the example covers the case.
    }
    
    inputs
  }
  

  /** Returns an instance of the given type */
  private def a(t: TypeTree): Expr = {
    all(t).head
  }
  
  /** Returns all instance of the given type */
  private def all(t: TypeTree): Stream[Expr] = {
    val i = FreshIdentifier("i", t)
    val datagen = new GrammarDataGen(new DefaultEvaluator(ctx, program), ValueGrammar)
    val enumerated_inputs = datagen.generateMapping(Seq(i), BooleanLiteral(true), 10, 10).toStream
    enumerated_inputs.toStream.map(_.head._2)
  }
  
  /** Returns an expression of the given type that contains at least a String, an Integer or an Int32 if possible. If not, returns None. */  
  private def buildMarkableValue(e: TypeTree): Option[Expr] = {
    var markableValues = Map[TypeTree, Expr]()
    
    val toTest = Queue[TypeTree](e)
    // Build all the types to test
    var finalTypes = Set[TypeTree]()
    
    while(toTest.nonEmpty) {
      val v = toTest.dequeue()
      v match {
        case cct@CaseClassType(ccd, targs) =>
          finalTypes += v
          for(tpe <- cct.fieldsTypes if !(finalTypes contains tpe) && !(toTest contains tpe)) {
            toTest.enqueue(tpe)
          }
        case act@AbstractClassType(acd, targs) =>
          finalTypes += v
          for(tpe <- act.knownCCDescendants if !(finalTypes contains tpe) && !(toTest contains tpe)) {
            toTest.enqueue(tpe)
          }
        case StringType | Int32Type | IntegerType =>
          markableValues += v -> a(v)
        case _ => 
      }
    }
    
    // Read all the types until all types have been flagged markable and non-markable.
    // All remaining are non-markable.
    
    var modified = true
    while(modified && !(markableValues contains e)) {
      modified = finalTypes find { tpe => 
        tpe match {
          case cct@CaseClassType(ccd, targs) =>
            cct.fields.find(t => markableValues contains t.getType) match {
              case Some(fieldId) =>
                markableValues += tpe -> CaseClass(cct, cct.fields.map(tpField =>
                  if(tpField == fieldId) markableValues(fieldId.getType) else a(tpField.getType)))
                finalTypes -= tpe
                true
              case None =>
                false
            }
          case act@AbstractClassType(acd, targs) =>
            act.knownCCDescendants.find(cc => markableValues contains cc) match {
              case None => false
              case Some(cc) =>
                markableValues += tpe -> markableValues(cc)
                finalTypes -= tpe
                true
            }
          case _ => false
        }
      } match {
        case Some(_) => true
        case None => false
      }
    }
    markableValues.get(e)
  }

  private def markWithStringOrInt(e: TypeTree, originalExpr: Expr): Option[Expr] = {
    buildMarkableValue(e).map{ value =>
      val Tuple(Seq(_, res)) = QuestionBuilder.makeGenericValuesUnique(Tuple(Seq(originalExpr, value)))
      res
    }
  }
}
