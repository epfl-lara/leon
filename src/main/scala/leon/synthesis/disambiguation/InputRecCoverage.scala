package leon
package synthesis.disambiguation

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

object InputRecCoverage {
  class W[T <: Expr](val e: T) {
    def somewhere(f: Expr): Boolean = e eq f
    // To ensure that the "equals" method of exprs is not used during the computation.
  }
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
    
    // Contains the set of top-level concatenations in all programs.
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
    
    // For each of these concatenations, we check that there is at least one input which if evaluated while it is reverse, the result would be different.
    // If not, we expand the covering example.
    
    val originalEvaluator = new DefaultEvaluator(ctx, program)
    var originalOutputs: Map[Seq[Expr], Expr] = inputs.map(input => input -> originalEvaluator.eval(functionInvocation(fd, input)).result.get).toMap
    for(stringConcatW <- concatenations; stringConcat = stringConcatW.e; stringConcatReversed <- permutations(stringConcat)) {
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
        // Now we need to find an input which makes a difference if possible, when modified.
        //println("No input make this concatenation differ in output when permutted: " + stringConcat + " -> " + stringConcatReversed)
        // First, make all its terminals (strings and numbers) unique.
        val covering = inputCoverage.getRecordMapping()
        val coveringInputs = covering.getOrDefault(stringConcat, Set()).map(x => identifiableInputs.getOrElse(x, x))
        //println(s"Input that can cover $stringConcat are " + coveringInputs.mkString(", "))
        
        val input = coveringInputs.head
        var mappingAtStringConcatOpt: Option[DefaultRecContext] = None
        val please = new DefaultEvaluator(ctx, program) {
          override def e(expr: Expr)(implicit rctx: RC, gctx: GC) = {
            if(expr eq stringConcat) {
              //println(s"Found string concat $stringConcat. Mapping = " + rctx)
              /*rctx.mappings.values.find{v =>
                  !input.exists(i => ExprOps.exists{ case e if e eq v => true case _ => false}(i))
              } match {
                case None =>
                case Some(v) =>
                  throw new Exception(s"Value not present from input ($input): $v")
                }*/
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
        for(m <- members) {
          m match {
            case FunctionInvocation(TypedFunDef(fd, targs), Seq(Variable(id))) =>
              mappingAtStringConcat.mappings.get(id) match {
                case Some(expr) =>
                  println(s"Mapping $m is computed on $expr")
                  // expr is a sub-expression of input.
                  // fd is the function called with the argument expr.
                  if(!isMarkedWithStringOrInt(expr)) {
                    val mainArg = fd.paramIds(0)
                    mainArg.getType match {
                      case act@AbstractClassType(acd, targs) =>
                        if(canBeMarkedWithStringOrInt(act)) {
                          val expr_marked = markWithStringOrInt(act, tupleWrap(input))
                          println(s"Expr unisized: $expr_marked")
                          /*if(!input.exists(i => ExprOps.exists{ case e if e eq expr => true case _ => false}(i))) {
                            throw new Exception(s"Did not find $expr (${expr.##}) in $input")
                          }*/
                          val new_input = input.map(i => ExprOps.postMap{ case e if e /*eq */ == expr => Some(expr_marked) case _ => None}(i))
                          println(s"Added new input: $new_input")
                          originalOutputs += new_input -> originalEvaluator.eval(functionInvocation(fd, input)).result.get
                          newInput = newInput :+ new_input
                        } else {
                          
                        }
                      case CaseClassType(ccd, targs) =>
                        
                      case StringType => // Nothing to do, the string is already unique.
                      case IntegerType => // Nothing to do, the int is already unique.
                      case t: TypeParameter => // Nothing to do, the type parameter is already unique
                      case Int32Type => // Nothing to do, the type parameter is already unique.
                      case BooleanType =>
                      case CharType =>
                    }
                  } // Else nothing to do, there is already a unique identifier to expr.
                  
                case None => throw new Exception(s"No binding at evaluation time for $id ... something is wrong.")
              }
            case IntegerToString(k) => // Nothing to do, already identified
            case Int32ToString(i) => // Nothing to do, already identified
            case BooleanToString(b) => // TODO: Enumerate all possible values
            case CharToString(c) => // Nothing to do, already identified
            case Variable(id) => // TODO: Enumerate all possible values of this id or have an identifiable one ?
            case StringLiteral(k) => // Nothing to do, already identified
            case e => throw new Exception(s"Rec-coverage is not supported when concatenating something else than fun(id) and constants; got $m")
          }
          
        }
        inputs = inputs.flatMap{ i => if(i == input) newInput else Some(input) }
        // Now we find which arguments are given to the function 
        
      } // Else that's fine, the example covers the case.
    }
    
    inputs
  }
  
  def isMarkedWithStringOrInt(e: Expr) =
     ExprOps.exists{
      case StringLiteral(_) => true
      case InfiniteIntegerLiteral(_) => true
      case IntLiteral(_) => true
      case _ => false
    }(e)
  
  def canBeMarkedWithStringOrInt(e: TypeTree): Boolean = {
    TypeOps.exists{
      case StringType => true
      case Int32Type => true
      case IntegerType => true
      case CaseClassType(ccd, targs) =>
        ccd.fieldsIds.exists(id => canBeMarkedWithStringOrInt(id.getType))
      case _ => false
    }(e)
  }
    
  def a(t: TypeTree): Expr = {
    val i = FreshIdentifier("i", t)
    val datagen = new GrammarDataGen(new DefaultEvaluator(ctx, program), ValueGrammar)
    val enumerated_inputs = datagen.generateMapping(Seq(i), BooleanLiteral(true), 1, 1).next()
    enumerated_inputs.head._2
  }
    
  def markWithStringOrInt(e: TypeTree, originalExpr: Expr): Expr = {
    // TODO: Make more generic
    val res = e match {
      case AbstractClassType(acd, targs) =>
        acd.knownCCDescendants.find(ccd => CaseClassType(ccd, targs).fieldsTypes.exists(t => t == StringType)) match {
          case Some(ccd) =>
            val Tuple(Seq(_, res)) = QuestionBuilder.makeGenericValuesUnique(Tuple(Seq(originalExpr, a(CaseClassType(ccd, targs)))))
            res
          case None => throw new Exception("Please make this funciton more generic")
        }
      case CaseClassType(ccd, targs) =>
        throw new Exception("Please make this funciton more generic - Right now does not support case class in argument")
    }
    println(s"About to return $e : $res")
    res
  }
}