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
import leon.utils.StreamUtils
import leon.synthesis.RulePriority
import leon.evaluators.AbstractEvaluator

/** A template generator for a given type tree. 
  * Extend this class using a concrete type tree,
  * Then use the apply method to get a hole which can be a placeholder for holes in the template.
  * Each call to the `.instantiate` method of the subsequent Template will provide different instances at each position of the hole.
  */
abstract class TypedTemplateGenerator(t: TypeTree) {
  import StringRender.WithIds
  /** Provides a hole which can be used multiple times in the expression.
    * When calling .instantiateWithVars on the results, replaces each hole by a unique constant.*/
  def apply(f: Expr => Expr): TemplateGenerator = {
    val id = FreshIdentifier("ConstToInstantiate", t, true)
    new TemplateGenerator(f(Variable(id)), id, t)
  }
  def nested(f: Expr => WithIds[Expr]): TemplateGenerator = {
    val id = FreshIdentifier("ConstToInstantiate", t, true)
    val res = f(Variable(id))
    new TemplateGenerator(res._1, id, t, res._2)
  }
  class TemplateGenerator(template: Expr, varId: Identifier, t: TypeTree, initialHoles: List[Identifier] = Nil) {
    private val optimizationVars = ListBuffer[Identifier]() ++= initialHoles
    private def Const: Variable = {
      val res = FreshIdentifier("const", t, true)
      optimizationVars += res
      Variable(res)
    }
    private def instantiate: Expr = {
      ExprOps.postMap({
        case Variable(id) if id == varId => Some(Const)
        case _ => None
      })(template)
    }
    def instantiateWithVars: WithIds[Expr] = (instantiate, optimizationVars.toList)
  }
}

/**
 * @author Mikael
 */
case object StringRender extends Rule("StringRender") {
  override val priority = RulePriorityPreprocessing
  
  // A type T augmented with a list of identifiers, for examples the free variables inside T
  type WithIds[T] = (T, List[Identifier])
  
  def EDIT_ME(n: Int): String = "_edit_me"+n+"_"
  val EDIT_ME_REGEXP = "_edit_me\\d+_".r
  val EDIT_ME_REGEXP_MULTIPLE = "(?:_edit_me\\d+_)+".r
  def contains_EDIT_ME(s: String): Boolean = EDIT_ME_REGEXP.findFirstIn(s).nonEmpty
  
  var enforceDefaultStringMethodsIfAvailable = true
  var enforceSelfStringMethodsIfAvailable = false
  
  val booleanTemplate = (a: Expr) => StringTemplateGenerator(Hole => IfExpr(a, Hole, Hole))
  
  import StringSolver.{StringFormToken, Problem => SProblem, Equation, Assignment}
  
  /** Augment the left-hand-side to have possible function calls, such as x + "const" + customToString(_) ...
   *  Function calls will be eliminated when converting to a valid problem.
   */
  sealed abstract class AugmentedStringFormToken
  case class RegularStringFormToken(e: StringFormToken) extends AugmentedStringFormToken
  case class OtherStringFormToken(e: Expr) extends AugmentedStringFormToken
  type AugmentedStringForm = List[AugmentedStringFormToken]
  
  /** Augments the right-hand-side to have possible function calls, such as "const" + customToString(_) ... 
   *  Function calls will be eliminated when converting to a valid problem.
   */
  sealed abstract class AugmentedStringChunkRHS
  case class RegularStringChunk(e: String) extends AugmentedStringChunkRHS
  case class OtherStringChunk(e: Expr) extends AugmentedStringChunkRHS
  type AugmentedStringLiteral = List[AugmentedStringChunkRHS]
  
  /** Converts an expression to a stringForm, suitable for StringSolver */
  def toStringForm(e: Expr, isVariableToLookFor: Identifier => Boolean, acc: List[AugmentedStringFormToken] = Nil)(implicit hctx: SearchContext): Option[AugmentedStringForm] = e match {
    case StringLiteral(s) => 
      Some(RegularStringFormToken(Left(s))::acc)
    case Variable(id) if isVariableToLookFor(id) => Some(RegularStringFormToken(Right(id))::acc)
    case v@Variable(id) => Some(OtherStringFormToken(v)::acc)
    case StringConcat(lhs, rhs) => 
      toStringForm(rhs, isVariableToLookFor, acc).flatMap(toStringForm(lhs, isVariableToLookFor, _))
    case e:Application => Some(OtherStringFormToken(e)::acc)
    case e:FunctionInvocation => Some(OtherStringFormToken(e)::acc)
    case _ => None
  }
  
  /** Returns the string associated to the expression if it is computable */
  def toStringLiteral(e: Expr, isVariableToLookFor: Identifier => Boolean): Option[AugmentedStringLiteral] = e match {
    case StringLiteral(s) => Some(List(RegularStringChunk(s)))
    case StringConcat(lhs, rhs) =>
      toStringLiteral(lhs, isVariableToLookFor).flatMap(k => toStringLiteral(rhs, isVariableToLookFor).map(l => (k.init, k.last, l) match {
        case (kinit, RegularStringChunk(s), RegularStringChunk(sp)::ltail) =>
          kinit ++ (RegularStringChunk(s + sp)::ltail)
        case _ => k ++ l
      }))
    case e: Variable if(!isVariableToLookFor(e.id)) => Some(List(OtherStringChunk(e)))
    case e: Application => Some(List(OtherStringChunk(e)))
    case e: FunctionInvocation => Some(List(OtherStringChunk(e)))
    case _ => None
  }
  
  /** Converts an equality AugmentedStringForm == AugmentedStringLiteral to a list of equations
   *  For that, splits both strings on function applications. If they yield the same value, we can split, else it fails. */
  def toEquations(lhs: AugmentedStringForm, rhs: AugmentedStringLiteral): Option[List[Equation]] = {
    def rec(lhs: AugmentedStringForm, rhs: AugmentedStringLiteral,
        accEqs: ListBuffer[Equation], accLeft: ListBuffer[StringFormToken], accRight: StringBuffer): Option[List[Equation]] = (lhs, rhs) match {
      case (Nil, Nil) =>
        (accLeft.toList, accRight.toString) match {
          case (Nil, "") => Some(accEqs.toList)
          case (lhs, rhs) => Some((accEqs += ((lhs, rhs))).toList)
        }
      case (OtherStringFormToken(e)::lhstail, OtherStringChunk(f)::rhstail) =>
        if(ExprOps.canBeHomomorphic(e, f).nonEmpty) {
          rec(lhstail, rhstail, accEqs += ((accLeft.toList, accRight.toString)), ListBuffer[StringFormToken](), new StringBuffer)
        } else None
      case (OtherStringFormToken(e)::lhstail, Nil) =>
        None
      case (Nil, OtherStringChunk(f)::rhstail) =>
        None
      case (lhs, RegularStringChunk(s)::rhstail) =>
        rec(lhs, rhstail, accEqs, accLeft, accRight append s)
      case (RegularStringFormToken(e)::lhstail, rhs) =>
        rec(lhstail, rhs, accEqs, accLeft += e, accRight)
    }
    rec(lhs, rhs, ListBuffer[Equation](), ListBuffer[StringFormToken](), new StringBuffer)
  }
  
  /** Returns a string equation problem corresponding to input/output examples for the given template */
  def extractStringProblem(p: Program, inputs: Seq[Identifier], examples: ExamplesBank, template: Expr, variablesToReplace: Set[Identifier])(implicit hctx: SearchContext): Option[StringSolver.Problem] = {
    //println(s"finding assignments in program\n$p")
    val e = new AbstractEvaluator(hctx, p)
    
    @tailrec def gatherEquations(s: List[InOutExample], acc: ListBuffer[Equation] = ListBuffer()): Option[SProblem] = s match {
      case Nil => Some(acc.toList)
      case InOutExample(in, rhExpr)::q =>
        if(rhExpr.length == 1) {
          val model = new ModelBuilder
          model ++= inputs.zip(in)
          val modelResult = model.result()
          val evalResult =  e.eval(template, modelResult)
          evalResult.result match {
            case None =>
              hctx.reporter.info("Eval = None : ["+template+"] in ["+inputs.zip(in)+"]")
              hctx.reporter.info(evalResult)
              None
            case Some((sfExpr, abstractSfExpr)) =>
              //ctx.reporter.debug("Eval = ["+sfExpr+"] (from "+abstractSfExpr+")")
              val sf = toStringForm(sfExpr, variablesToReplace)
              val rhs = toStringLiteral(rhExpr.head, variablesToReplace)
              (sf, rhs) match {
                case (Some(sfget), Some(rhsget)) =>
                  toEquations(sfget, rhsget) match {
                    case Some(equations) =>
                      gatherEquations(q, acc ++= equations)
                    case None =>
                      hctx.reporter.info("Could not extract equations from ["+sfget+"] == ["+rhsget+"]\n coming from ... == " + rhExpr)
                    None
                  }
                case _ =>
                  hctx.reporter.info("sf empty or rhs empty ["+sfExpr+"] = ["+rhExpr+"] => ["+sf+"] == ["+rhs+"]")
                  None
              }
          }
        } else {
          hctx.reporter.info("RHS.length != 1 : ["+rhExpr+"]")
          None 
        }
    }
   
    gatherEquations((examples.valids ++ examples.invalids).collect{ case io:InOutExample => io }.toList)
  }
  
  /** Returns a stream of assignments compatible with input/output examples for the given template */
  def findAssignments(p: Program, inputs: Seq[Identifier], examples: ExamplesBank, template: Expr, variablesToReplace: Set[Identifier])(implicit hctx: SearchContext): Stream[Map[Identifier, String]] = {
    extractStringProblem(p, inputs, examples, template, variablesToReplace) match {
      case Some(problem) =>
        StringSolver.solve(problem)
      case None => Stream.empty
    }
  }
  
  /** With a given (template, fundefs, consts) will find consts so that (expr, funs) passes all the examples */
  def findSolutions(examples: ExamplesBank,
                    templateFunDefs: Stream[(WithIds[Expr], Seq[(FunDef, Stream[WithIds[Expr]])])])(implicit hctx: SearchContext, p: Problem): RuleApplication = {
    // Fun is a stream of many function applications.
    val funs = templateFunDefs.map{ case (template, funDefs) =>
      val funDefsSet = JoinProgramSet.direct(funDefs.map(fbody => fbody._2.map((fbody._1, _))).map(d => DirectProgramSet(d)))
      JoinProgramSet.direct(funDefsSet, DirectProgramSet(Stream(template))).programs
    }
    
    val wholeTemplates = StreamUtils.interleave(funs)
    
    def computeSolutions(funDefsBodies: Seq[(FunDef, WithIds[Expr])], template: WithIds[Expr]): Stream[Assignment] = {
      val funDefs = for((funDef, body) <- funDefsBodies) yield  { funDef.body = Some(body._1); funDef }
      val newProgram = DefOps.addFunDefs(hctx.program, funDefs, hctx.functionContext)
      val transformer = DefOps.funDefReplacer { fd =>
        if(fd == hctx.functionContext) {
          val newfd = fd.duplicate()
          newfd.body = Some(template._1)
          Some(newfd)
        } else None
      }
      val newProgram2 = DefOps.transformProgram(transformer, newProgram)
      val newTemplate = ExprOps.postMap{
        case FunctionInvocation(TypedFunDef(fd, targs), exprs) =>
          Some(FunctionInvocation(TypedFunDef(transformer.transform(fd), targs), exprs))
        case _ => None
      }(template._1)
      val variablesToReplace = (template._2 ++ funDefsBodies.flatMap(_._2._2)).toSet
      findAssignments(newProgram2, p.as.filter{ x => !x.getType.isInstanceOf[FunctionType] }, examples, newTemplate, variablesToReplace)
    }
    
    val tagged_solutions =
      for{(funDefs, template) <- wholeTemplates} yield computeSolutions(funDefs, template).map((funDefs, template, _))
    
    solutionStreamToRuleApplication(p, leon.utils.StreamUtils.interleave(tagged_solutions))(hctx.program)
  }

  /** Converts the stream of solutions to a RuleApplication */
  def solutionStreamToRuleApplication(p: Problem, solutions: Stream[(Seq[(FunDef, WithIds[Expr])], WithIds[Expr], Assignment)])(implicit program: Program): RuleApplication = {
    if(solutions.isEmpty) RuleFailed() else {
      RuleClosed(
          for((funDefsBodies, (singleTemplate, ids), assignment) <- solutions) yield {
            var _i = 0
            def i = { _i += 1; _i }
            val fds = for((fd, (body, ids)) <- funDefsBodies) yield {
              val initMap = ids.map(_ -> StringLiteral(EDIT_ME(i))).toMap
              fd.body = Some(ExprOps.simplifyString(ExprOps.replaceFromIDs(initMap ++ assignment.mapValues(StringLiteral), body)))
              fd
            }
            val initMap = ids.map(_ -> StringLiteral(EDIT_ME(i))).toMap
            val term = ExprOps.simplifyString(ExprOps.replaceFromIDs(initMap ++ assignment.mapValues(StringLiteral), singleTemplate))
            val (finalTerm, finalDefs) = makeFunctionsUnique(term, fds.toSet)
            
            Solution(BooleanLiteral(true), finalDefs, finalTerm)
          })
    }
  }
  
  /** Crystallizes a solution so that it will not me modified if the body of fds is modified. */
  def makeFunctionsUnique(term: Expr, fds: Set[FunDef])(implicit program: Program): (Expr, Set[FunDef]) = {
    var transformMap = Map[FunDef, FunDef]()
    def mapExpr(body: Expr): Expr = {
      ExprOps.preMap((e: Expr) => e match {
        case FunctionInvocation(TypedFunDef(fd, _), args) if fds(fd) => Some(functionInvocation(getMapping(fd), args))
        case e => None
      })(body)
    }
    
    def getMapping(fd: FunDef): FunDef = {
      transformMap.getOrElse(fd, {
        val newfunDef = new FunDef(fd.id.freshen, fd.tparams, fd.params, fd.returnType) // With empty body
        transformMap += fd -> newfunDef
        newfunDef.body = fd.body.map(mapExpr _)
        newfunDef
      })
    }
    
    (mapExpr(term), fds.map(getMapping _))
  }
  
  
  object StringTemplateGenerator extends TypedTemplateGenerator(StringType)
  
  trait FreshFunNameGenerator {
    def funNames: Set[String]
    def freshFunName(s: String): String = {
      if(!funNames(s)) return s
      var i = 1
      var s0 = s
      do {
        i += 1
        s0 = s + i
      } while(funNames(s+i))
      s0
    }
  }
  trait PrettyPrinterProvider {
    def provided_functions: Seq[Identifier]
  }
  type StringConverters = Map[TypeTree, List[Expr => Expr]]
  
  /** Creates an empty function definition for the dependent type */
  def createEmptyFunDef(ctx: FreshFunNameGenerator with PrettyPrinterProvider, vContext: List[TypeTree], hContext: List[TypeTree], typeToConvert: TypeTree)(implicit hctx: SearchContext): FunDef = {
    def defaultFunName(t: TypeTree): String = t match {
      case AbstractClassType(c, d) => c.id.asString(hctx)
      case CaseClassType(c, d) => c.id.asString(hctx)
      case t => t.asString(hctx)
    }
    
    val funName2 = defaultFunName(typeToConvert) + ("" /: vContext) {
      case (s, t) => "In" + defaultFunName(t)
    } + (if(hContext.nonEmpty) hContext.length.toString else "") + "_s" 
    val funName3 = funName2.replaceAll("[^a-zA-Z0-9_]","")
    val funName = funName3(0).toLower + funName3.substring(1) 
    val funId = FreshIdentifier(ctx.freshFunName(funName), alwaysShowUniqueID = false)
    val argId= FreshIdentifier(typeToConvert.asString(hctx).toLowerCase().dropWhile(c => (c < 'a' || c > 'z') && (c < 'A' || c > 'Z')).headOption.getOrElse("x").toString, typeToConvert)
    val tparams = hctx.functionContext.tparams
    new FunDef(funId, tparams, ValDef(argId) :: ctx.provided_functions.map(ValDef(_)).toList, StringType) // Empty function.
  }
  
  /** Assembles multiple MatchCase to a singleMatchExpr using the function definition fd */
  private val mergeMatchCases = (scrut: Expr) => (cases: Seq[WithIds[MatchCase]]) => (MatchExpr(scrut, cases.map(_._1)), cases.flatMap(_._2).toList)
  private val mergeMatchCasesFd = (fd: FunDef) => mergeMatchCases(Variable(fd.params(0).id))
  
  object FunDefTemplateGenerator {
    protected val gcontext = new grammars.ContextGrammar[TypeTree, (Program, Set[FunDef]) => Stream[Expr => WithIds[Expr]]]
    import gcontext._
    
    protected val int32Symbol   = NonTerminal(Int32Type)
    protected val integerSymbol = NonTerminal(IntegerType)
    protected val booleanSymbol = NonTerminal(BooleanType)
    protected val stringSymbol  = NonTerminal(StringType)
    protected val bTemplateGenerator = (expr: Expr) => booleanTemplate(expr).instantiateWithVars
    
    // The pretty-printers are variable passed along in argument that have a type T => String for some type parameter T
    def apply(argsInputs: Seq[Expr], argsPrettyPrinting: Seq[Identifier])(implicit hctx: SearchContext): GrammarBasedTemplateGenerator = { 
      implicit val program: Program = hctx.program
      val startGrammar = Grammar(
        (argsInputs.foldLeft(List[NonTerminal]()){(lb, i) => lb :+ NonTerminal(i.getType) }),
        Map(int32Symbol -> TerminalRHS(Terminal(Int32Type)((prog, fds)=> Stream(expr => (Int32ToString(expr), Nil)))),
            integerSymbol -> TerminalRHS(Terminal(IntegerType)((prog, fds) => Stream((expr => (IntegerToString(expr), Nil))))),
            booleanSymbol -> TerminalRHS(Terminal(BooleanType)((prog, fds) => Stream((expr => (BooleanToString(expr), Nil)), bTemplateGenerator))),
            stringSymbol -> TerminalRHS(Terminal(StringType)((prog, fds) => Stream((expr => (expr, Nil)),(expr => ((FunctionInvocation(program.library.escape.get.typed, Seq(expr)), Nil)))))
        )))
      GrammarBasedTemplateGenerator(clean(exhaustive(startGrammar, argsPrettyPrinting)), argsInputs, argsPrettyPrinting)
    }
    
    case class GrammarBasedTemplateGenerator(grammar: Grammar, argsInputs: Seq[Expr], argsPrettyPrinting: Seq[Identifier])(implicit hctx: SearchContext) {
      /** Use with caution: These functions make the entire grammar increase exponentially in size*/
      def markovize_vertical() = copy(grammar=grammar.markovize_vertical())
      def markovize_horizontal() = copy(grammar=grammar.markovize_horizontal())
      def markovize_abstract_vertical() = copy(grammar=grammar.markovize_abstract_vertical())
      
      /** Mark all occurrences of a given type so that we can differentiate its usage according to its rank from the left.*/
      def markovize_horizontal_nonterminal() = {
        val selectedNt = getDuplicateCallsInSameRule()
        //println("markovize_horizontal_nonterminal with "+selectedNt.map(symbolToString)+"...")
        copy(grammar=grammar.markovize_horizontal_filtered(selectedNt, false))
      }
      /** Mark all occurrences of a given type so that we can differentiate its usage according to its rank from the left.*/
      def markovize_horizontal_recursive_nonterminal() = {
        val selectedNt = getDuplicateCallsInSameRule()
        //println("markovize_horizontal_nonterminal with "+selectedNt.map(symbolToString)+"...")
        copy(grammar=grammar.markovize_horizontal_filtered(selectedNt, true))
      }
      
      /** Mark all occurrences of a given type so that we can differentiate its usage depending from where it was taken from.*/
      def markovize_abstract_vertical_nonterminal() = {
        //println("markovize_abstract_vertical_nonterminal...")
        val selectedNt = getDirectlyRecursiveTypes()
        copy(grammar=grammar.markovize_abstract_vertical_filtered(selectedNt))
      }
      
      /** Interruptible stream*/
      def interruptibleStreamFrom(n: Int): Stream[Int] =
        n #:: (if(hctx.interruptManager.isInterrupted) Stream.empty else interruptibleStreamFrom(n+1))
      
      /** Computes all possible variants of the grammar, from the simplest to the most complex.*/
      def allMarkovizations(): Stream[GrammarBasedTemplateGenerator] = {
        interruptibleStreamFrom(1).flatMap(i =>
          grammar.markovize_all(i).filter(_ => !hctx.interruptManager.isInterrupted).map(g => copy(grammar=g)))
      }
      
      /** Mark all occurrences of a given type so that we can differentiate its usage depending from where it was taken from.*/
      def markovize_vertical_nonterminal() = {
        //println("markovize_vertical_nonterminal...")
        val selectedNt = getTypesAppearingAtMultiplePlaces()
        copy(grammar=grammar.markovize_vertical_filtered(selectedNt))
      }

      def getAllTypes(): Set[TypeTree] = {
        grammar.rules.keys.map(_.tag).toSet
      }
      
      /** Monitoring data in the grammar */
      // Find all non-terminals which have a rule that use this type tree.
      def getCallsfor(e: TypeTree): Seq[(NonTerminal, Expansion)] = {
        grammar.rules.toSeq.filter{ case (k, v) => v.ls.exists(l => l.exists ( _.tag == e ))}
      }
      // Find all non-terminals which have the type tree on the RHS at least twice in the same rule.
      // Used for horizontal markovization
      def getDuplicateCallsInSameRule(): Set[NonTerminal] = {
        def duplicates(l: List[Symbol], e: TypeTree) = {
          val lnt = l.collect{case nt: NonTerminal => nt}
            if(lnt.count ( _.tag == e ) >= 2) {
              lnt.filter(_.tag == e)
            } else Nil
        }
        getAllTypes().flatMap { e => 
          grammar.rules.toSeq.flatMap{ case (k, v) =>
            v.ls.flatMap{l => duplicates(l, e) }
          }.toSet ++ duplicates(grammar.start.toList, e)
        }
      }
      // Return types which call themselves in argument (and which might require vertical markovization to differentiate between an inner call and an outer call).
      // Used for vertical markovization
      def getDirectlyRecursiveTypes(): Set[NonTerminal] = {
        grammar.rules.toSeq.flatMap{ case (k, v) => if(v match {
          case AugmentedTerminalsRHS(_, VerticalRHS(children)) => children.exists(child => grammar.rules(child) match {
            case AugmentedTerminalsRHS(_, HorizontalRHS(t, arguments)) => arguments.exists(_ == k)
            case _ => false
          })
          case _ => false})
          Seq(k) else Nil
        }.toSet
      }
      // Returns non-terminals which appear on different RHS of different rules, and which require vertical markovization.
      def getTypesAppearingAtMultiplePlaces(): Set[NonTerminal] = {
        (grammar.rules.toSeq.flatMap{ case (k, v) =>
          v.ls.flatten
        } ++ grammar.startNonTerminals).
        groupBy { s => s }.
        toSeq.
        map(_._2).
        filter(_.length >= 2).
        flatMap(_.headOption).
        collect{ case t: NonTerminal => t}.
        toSet
      }
      
      def buildAllFunDefTemplates(): Stream[(WithIds[Expr], Seq[(FunDef, Stream[WithIds[Expr]])])] = {
        allMarkovizations().flatMap(_.buildFunDefTemplate(false))
      }
      
      /** Builds a set of fun defs out of the grammar */
      def buildFunDefTemplate(markovizations: Boolean = true): Stream[(WithIds[Expr], Seq[(FunDef, Stream[WithIds[Expr]])])] = {
        if(hctx.interruptManager.isInterrupted) return Stream.empty
        // Collects all non-terminals. One non-terminal => One function. May regroup pattern matching in a separate simplifying phase.
        val nts = grammar.nonTerminals
        // Fresh function name generator.
        val ctx = new FreshFunNameGenerator with PrettyPrinterProvider {
          var funNames: Set[String] = Set()
          override def freshFunName(s: String): String = {
            val res = super.freshFunName(s)
            funNames += res
            res
          }
          def provided_functions = argsPrettyPrinting
        }
         // Matches a case class and returns its context type.
        object TypedNonTerminal {
          def unapply(nt: NonTerminal) = Some((nt.tag, nt.vcontext.map(_.tag), nt.hcontext.map(_.tag)))
        }
        /* We create FunDef for all on-terminals */
        val (funDefs, ctx2) = ((Map[NonTerminal, FunDef](), ctx) /: nts) {
          case (mgen@(m, genctx), nt@TypedNonTerminal(tp, vct, hct)) =>
            (m + ((nt: NonTerminal) -> createEmptyFunDef(genctx, vct, hct, tp)), genctx)
        }
        // Look for default ways to pretty-print non-trivial functions.
        val (newProg, newFuns) = //if(markovizations)
          {
          val functionsToAdd = funDefs.values.filter(fd =>
            fd.paramIds.headOption.map(x =>
              x.getType match {
                case AbstractClassType(acd, targs) => hctx.program.library.List.get != acd
                case _: MapType | _: SetType | _: BagType => false
                case _ => true
              }
            ).getOrElse(false)
          ).toSet
          (DefOps.addFunDefs(hctx.program, functionsToAdd, hctx.functionContext), functionsToAdd)
        } //else (hctx.program, Set[FunDef]())
        //println("In the following program: " + newProg)
        
        def rulesToBodies(e: Expansion, nt: NonTerminal, fd: FunDef): Stream[WithIds[Expr]] = {
          val inputs = fd.params.map(_.id)
          var customProgs: Stream[Expr => WithIds[Expr]] = Stream()
          def filteredPrintersOf(t: Terminal): Stream[Expr => WithIds[Expr]] = {
            val p = t.terminalData
            val newFunsFiltered = fd.paramIds.headOption.map(_.getType) match {
              case Some(forbiddenType) =>
                newFuns.filter(f =>
                  f.paramIds.headOption.map(x => !TypeOps.isSubtypeOf(forbiddenType, x.getType)).getOrElse(true))
              case None => newFuns
            }
            //println("For fun " + fd.id.name +", taking only " + newFunsFiltered.map(_.id.name) + " into account")
            p(newProg, newFunsFiltered)
          }
          def filteredPrintersOfAreNonEmpty(t: Terminal): Boolean = {
            customProgs = filteredPrintersOf(t)
            customProgs.nonEmpty
          }
          e match {
            case TerminalRHS(terminal@Terminal(typeTree)) if filteredPrintersOfAreNonEmpty(terminal) => //Render this as a simple expression.
              customProgs.map(f => f(Variable(inputs.head)))
            case AugmentedTerminalsRHS(terminals, HorizontalRHS(terminal@Terminal(cct@CaseClassType(ccd, targs)), nts)) => // The subsequent calls of this function to sub-functions.
              val fields = cct.classDef.fieldsIds.zip(cct.fieldsTypes)
              val fieldstypes = fields.map{ case (id, tpe) => (tpe, (x: Expr) => CaseClassSelector(cct, x, id)) }
              val builders = fieldstypes.flatMap(x => flattenTupleExtractors(x._1, x._2))
              
              val childExprs = nts.zipWithIndex.map{ case (childNt:NonTerminal, childIndex) =>
                FunctionInvocation(TypedFunDef(funDefs(childNt), Seq()), List(
                    builders(childIndex)(Variable(inputs.head))) ++
                    argsPrettyPrinting.map(Variable))
              }
              terminals.map(filteredPrintersOf).toStream.flatten.map(_.apply(Variable(inputs.head))) #::: childExprs.map(x => (x, Nil)).permutations.toStream.map(interleaveIdentifiers)
            case AugmentedTerminalsRHS(terminals, HorizontalRHS(terminal@Terminal(cct@TupleType(targs)), nts)) => // The subsequent calls of this function to sub-functions.
              val fieldstypes = targs.zipWithIndex.map{case (tp, index)  => (tp, (x: Expr) => TupleSelect(x, index+1)) }
              val builders = fieldstypes.flatMap(x => flattenTupleExtractors(x._1, x._2))
              
              val childExprs = nts.zipWithIndex.map{ case (childNt:NonTerminal, childIndex) =>
                FunctionInvocation(TypedFunDef(funDefs(childNt), Seq()), List(
                    builders(childIndex)(Variable(inputs.head))) ++
                    argsPrettyPrinting.map(Variable))
              }
              terminals.map(filteredPrintersOf).toStream.flatten.map(_.apply(Variable(inputs.head))) #::: childExprs.map(x => (x, Nil)).permutations.toStream.map(interleaveIdentifiers)
            case AugmentedTerminalsRHS(terminals, VerticalRHS(children)) => // Match statement.
              assert(inputs.length == 1 + argsPrettyPrinting.length)
              val idInput = inputs.head
              val scrut = Variable(idInput)
              val matchCases = nt.tag match {
                case AbstractClassType(acd, typeArgs) =>
                  acd.knownCCDescendants map { ccd => 
                    children.find(childNt => childNt.tag match {
                      case CaseClassType(`ccd`, `typeArgs`) => true
                      case _ => false
                    }) match {
                      case Some(nt) =>
                        val matchInput = idInput.duplicate(tpe = nt.tag)
                        MatchCase(InstanceOfPattern(Some(matchInput), nt.tag.asInstanceOf[ClassType]), None,
                            FunctionInvocation(TypedFunDef(funDefs(nt), Seq()), List(Variable(matchInput)) ++ argsPrettyPrinting.map(Variable)))
                      case None => throw new Exception(s"Could not find $ccd in the children non-terminals $children")
                    }
                  }
                case t =>
                  throw new Exception(s"Should have been Vertical RHS, got $t. Rule:\n$nt -> $e\nFunDef:\n$fd")
              }
              
              terminals.map(filteredPrintersOf).toStream.flatten.map(_.apply(Variable(inputs.head))) #::: Stream((MatchExpr(scrut, matchCases): Expr, Nil: List[Identifier]))
            case _ => throw new Exception("No toString conversion found for " + nt)
          }
        }
        
        //println("Extracting functions from grammar:\n" + grammarToString(grammar).replaceAll("\\$", "_").replaceAll("\\[T3\\]", "T3").replaceAll("\\(|\\)","").replaceAll("<function1>",""))
        
        // We create the bodies of these functions  
        val possible_functions = for((nt, fd) <- funDefs.toSeq) yield {
          val bodies: Stream[WithIds[Expr]] = rulesToBodies(grammar.rules(nt), nt, fd)
          (fd, bodies/*.map{ b => println("Testing another body for " + fd.id.name + "\n" + b); b}*/)
        }
        
        val inputExprs = grammar.startNonTerminals.zipWithIndex.map{ case (childNt, childIndex) =>
          (FunctionInvocation(TypedFunDef(funDefs(childNt), Seq()), Seq(argsInputs(childIndex)) ++ argsPrettyPrinting.map(Variable)), Nil)
        }
        //println("Found grammar\n" + grammarToString(grammar))
        
        val startExprStream = inputExprs.permutations.toStream.map(inputs =>
          interleaveIdentifiers(inputs)
        )
        
        startExprStream.map(i => (i, possible_functions)) #:::                 // 1) Expressions without markovizations
          (if(markovizations) {
              Stream(markovize_horizontal_recursive_nonterminal(), markovize_horizontal_nonterminal())
              .flatMap(grammar => grammar.buildFunDefTemplateAndContinue(
                  gtg => gtg.allMarkovizations().flatMap(m => m.buildFunDefTemplate(false))))
                //markovize_abstract_vertical_nonterminal().buildFunDefTemplateAndContinue( _.
                  //markovize_vertical_nonterminal().buildFunDefTemplate(false))))
          } else Stream.empty)
        // The Stream[WithIds[Expr]] is given thanks to the first formula with the start symbol.
        // The FunDef are computed by recombining vertical rules into one pattern matching, and each expression using the horizontal children.
      }
      
      def buildFunDefTemplateAndContinue(continueWith: GrammarBasedTemplateGenerator => (Stream[(WithIds[Expr], Seq[(FunDef, Stream[WithIds[Expr]])])])): (Stream[(WithIds[Expr], Seq[(FunDef, Stream[WithIds[Expr]])])]) = {
        buildFunDefTemplate(false) #::: (continueWith(this))
      }
    }
    
    protected def flattenTupleType(t: TypeTree): Seq[TypeTree] = {
      t match {
        case TupleType(targs) => targs.flatMap(flattenTupleType)
        case t => Seq(t)
      }
    }
    protected def flattenTupleExtractors(t: TypeTree, builder: Expr => Expr): Seq[Expr => Expr] = {
      t match {
        case TupleType(targs) => targs.zipWithIndex.flatMap{
          case (t, i) => flattenTupleExtractors(t, builder andThen ((x: Expr) => TupleSelect(x, i+1)))
        }
        case t => Seq(builder)
      }
    }
    
    protected def customPrettyPrinters(inputType: TypeTree, program: Program, allowedPrinters: Set[FunDef])(implicit hctx: SearchContext): List[Expr => WithIds[Expr]] = {
      val toExclude: Set[FunDef] = 
        if(hctx.functionContext.paramIds.headOption.map(x => TypeOps.isSubtypeOf(inputType, x.getType)).getOrElse(false))
          Set(hctx.functionContext)
        else
          Set()
      //println("Looking for pp of type " + inputType + ", excluded = " + toExclude.map(_.id.name) + ", allowed = " + allowedPrinters.map(_.id.name))
      val exprs1s: Stream[(Lambda, Expr => WithIds[Expr])] = (new SelfPrettyPrinter)
        .allowFunctions(allowedPrinters + hctx.functionContext)
        .excludeFunctions(toExclude + hctx.program.library.escape.get)
        .withPossibleParameters
        .prettyPrintersForType(inputType)(hctx, program)
        .map{ case (l, identifiers) => (l, (input: Expr) => (application(l, Seq(input)), identifiers)) } // Use already pre-defined pretty printers.
      val e = exprs1s.toList.sortBy{ case (Lambda(_, FunctionInvocation(tfd, _)), _) if tfd.fd == hctx.functionContext => 0 case _ => 1}.map(_._2)
      //println("looking for functions to print " + inputType + ", got " + e)
      e
    }
    
    def constantPatternMatching(act: AbstractClassType)(implicit hctx: SearchContext): Stream[Expr => WithIds[Expr]] = {
      val allKnownDescendantsAreCCAndHaveZeroArgs = act.knownCCDescendants.forall {
        case CaseClassType(ccd, tparams2) => ccd.fields.isEmpty
        case _ => false
      }
      //if(act.id.name == "ThreadId") println("For ThreadId, allKnownDescendantsAreCCAndHaveZeroArgs = " + allKnownDescendantsAreCCAndHaveZeroArgs)
      if(allKnownDescendantsAreCCAndHaveZeroArgs) {
        val cases = (ListBuffer[WithIds[MatchCase]]() /: act.knownCCDescendants) {
          case (acc, cct @ CaseClassType(ccd, tparams2)) =>
            val typeMap = ccd.typeArgs.zip(tparams2).toMap
            val fields = ccd.fields.map(vd => TypeOps.instantiateType(vd.id, typeMap) )
            val pattern = CaseClassPattern(None, ccd.typed(tparams2), fields.map(k => WildcardPattern(Some(k))))
            val rhs = StringLiteral(ccd.id.asString)
            MatchCase(pattern, None, rhs)
            acc += ((MatchCase(pattern, None, rhs), Nil))
          case (acc, e) => hctx.reporter.fatalError("Could not handle this class definition for string rendering " + e)
        }
        //if(act.id.name == "ThreadId") println("For ThreadId, cases = " + cases)
        if(cases.nonEmpty) {
          Stream((x: Expr) => mergeMatchCases(x)(cases))
        } else Stream.Empty
      } else Stream.Empty
    }
    
    /** Used to produce rules such as Cons => Elem List without context*/
    protected def horizontalChildren(n: NonTerminal)(implicit hctx: SearchContext): Option[Expansion] = n match {
      case NonTerminal(cct@CaseClassType(ccd: CaseClassDef, tparams2), vc, hc) =>
        val flattenedTupleds = cct.fieldsTypes.flatMap(flattenTupleType)
        val customs = (p: Program, fds: Set[FunDef]) => customPrettyPrinters(cct, p,fds).toStream
        Some(AugmentedTerminalsRHS(Seq(Terminal(cct)(customs)),
              HorizontalRHS(Terminal(cct)((prog, fds) => Stream.empty), flattenedTupleds.map(NonTerminal(_)))))
      case NonTerminal(cct@TupleType(fieldsTypes), vc, hc) => 
        val flattenedTupleds = fieldsTypes.flatMap(flattenTupleType)
        val customs = (p: Program, fds: Set[FunDef]) => customPrettyPrinters(cct, p, fds).toStream
        Some(AugmentedTerminalsRHS(Seq(Terminal(cct)(customs)),
              HorizontalRHS(Terminal(cct)((prog, fds) => Stream.empty), flattenedTupleds.map(NonTerminal(_)))))
      case NonTerminal(otherType, vc, hc) if !otherType.isInstanceOf[AbstractClassType] =>
        val customs = (p: Program, fds: Set[FunDef]) => customPrettyPrinters(otherType, p, fds).toStream
        //if(customs.nonEmpty) {
          Some(AugmentedTerminalsRHS(Seq(Terminal(otherType)(customs)),
              TerminalRHS(Terminal(otherType)((prog, fds) => Stream.empty))))
        //} else None
      case _ => None
    }
    /** Used to produce rules such as List => Cons | Nil without context */
    protected def verticalChildren(n: NonTerminal)(implicit hctx: SearchContext): Option[Expansion] = n match {
      case NonTerminal(act@AbstractClassType(acd: AbstractClassDef, tps), vc, hc) => 
        //if(act.id.name == "ThreadId") println("Creating custom pretty printers for type ThreadId")
        val customs = (p: Program, fds: Set[FunDef]) => constantPatternMatching(act) #::: customPrettyPrinters(act, p, fds).toStream
        Some(AugmentedTerminalsRHS(Seq(Terminal(act)(customs)),
            VerticalRHS(act.knownDescendants.map(tag => NonTerminal(tag)))))
      case _ => None
    }
    
    /** Find all direct calls to existing variables render the given type */
    protected def terminalChildren(n: NonTerminal, prettyPrinters: Seq[Identifier]): Option[Expansion] = n match {
      case NonTerminal(tp: TypeParameter, vc, hc) =>
        val possible_pretty_printers = prettyPrinters.map(x => (x, x.getType)).collect{ case (id, FunctionType(tp, StringType)) => id}
        val callers = possible_pretty_printers.toStream.map{
          case id => (x: Expr) => (Application(Variable(id), Seq(x)), Nil)
        }
        Some(TerminalRHS(Terminal(tp)((p, fds) => callers)))
      case _ => None
    }
    
    /** Find all dependencies and merge them into one grammar */
    protected def extendGrammar(prettyPrinters: Seq[Identifier])(grammar: Grammar)(implicit hctx: SearchContext): Grammar = {
      val nts = grammar.nonTerminals
      (grammar /: nts) {
        case (grammar, n) =>
          /** If the grammar does not contain any rule for n, add them */
          if(!(grammar.rules contains n)) {
            grammar.copy(rules =
              grammar.rules +
                (n -> (
                    Expansion(Nil) ++
                    terminalChildren(n, prettyPrinters) ++ 
                    horizontalChildren(n) ++
                    verticalChildren(n))))
          } else grammar
      }
    }
    
    /** Applies the transformation extendGrammar until the grammar reaches its fix point. */
    protected def exhaustive(grammar: Grammar, prettyPrinters: Seq[Identifier])(implicit hctx: SearchContext): Grammar = {
      leon.utils.fixpoint(extendGrammar(prettyPrinters))(grammar)
    }
  }
  
  /** Transforms a sequence of identifiers into a single expression
    * with new string constant identifiers interleaved between, before and after them. */
  def interleaveIdentifiers(exprs: Seq[WithIds[Expr]]): WithIds[Expr] = {
    if(exprs.isEmpty) {
      StringTemplateGenerator(Hole => Hole).instantiateWithVars
    } else {
      StringTemplateGenerator.nested(Hole => {
        val res = ((StringConcat(Hole, exprs.head._1), exprs.head._2) /: exprs.tail) {
          case ((finalExpr, finalIds), (expr, ids)) => (StringConcat(StringConcat(finalExpr, Hole), expr), finalIds ++ ids)
        }
        (StringConcat(res._1, Hole), res._2)
      }).instantiateWithVars
    }
  }
  
  def repair(p: Problem, examples: ExamplesBank, guide: Expr)(implicit hctx: SearchContext): RuleApplication = {
    val initialMappingBuilder = ListBuffer[(Identifier, String)]()
    // Functions (inc. the original one if directly recursive) which are called and inlined in the context function's body
    var initmodifiableFunDefs = DefOps.getAllInlineFunctionInvocations(guide, hctx.functionContext)
    // All inline functions (inc. the original one if recursive) which are called and inline in the context function's body
    val modifiableFunDefs = DefOps.getAllReachableInlineFunctions(hctx.functionContext, initmodifiableFunDefs)
    // Fun to convert strings literals to variables and record the mappings.
    val stringsToVariables = ExprOps.preMap{
      case StringLiteral(a) =>
        val c = FreshIdentifier("X", StringType, true)
        initialMappingBuilder += c -> a
        Some(Variable(c))
      case _ => None
    } _

    var fundefMapping = Map[FunDef, FunDef]()
    val (newProgram, newGuideTemplate, maybeTransformer) = if(modifiableFunDefs.nonEmpty) {
      val transformer = DefOps.funDefReplacer { fd =>
        if(modifiableFunDefs contains fd) {
          val newfd = fd.duplicate()
          newfd.body = fd.body.map(stringsToVariables)
          fundefMapping += fd -> newfd
          Some(newfd)
        } else None
      }
      val newProgram2 = DefOps.transformProgram(transformer, hctx.program)
      val newGuideTemplate2 = if(modifiableFunDefs contains hctx.functionContext)
           fundefMapping(hctx.functionContext).body.get
      else transformer.transform(stringsToVariables(guide))(Map())
      (newProgram2, newGuideTemplate2, Some(transformer))
    } else // if not recursive and no inline functions called.
      (hctx.program, stringsToVariables(guide), None)
    val initialMapping: StringSolver.Assignment = initialMappingBuilder.toMap
    val problem: StringSolver.Problem  =
      extractStringProblem(newProgram, p.as, examples, newGuideTemplate, initialMapping.keySet) match {
      case Some(p) => p
      case None =>
        hctx.reporter.debug("Could not extract string problem from " + newGuideTemplate)
        return RuleClosed(Stream.Empty)
    }
    val solutions = StringSolver.solveMinChange(problem, initialMapping)
    
    def applySolution(solution: StringSolver.Assignment)(input: Expr): Expr = {
      ExprOps.preMap{
        case Variable(i) if solution contains i => Some(StringLiteral(solution(i)))
        case Variable(i) if initialMapping contains i => Some(StringLiteral(initialMapping(i)))
        case _ => None
      }(input)
    }
    
    val recoverOriginalRecursiveFunction = if(modifiableFunDefs contains hctx.functionContext) {
      ExprOps.preMap{
        case FunctionInvocation(tfd, args) if tfd.fd == fundefMapping(hctx.functionContext) =>
          Some(FunctionInvocation(hctx.functionContext.typed(tfd.tps), args))
        case _ => None
      } _
    } else (s: Expr) => s

    RuleClosed(
       solutions.map{solution => 
         val assignedGuideTemplate = recoverOriginalRecursiveFunction(applySolution(solution)(newGuideTemplate))
         var prevBodies = Map[FunDef, Option[Expr]]()
         val solutionFds: Set[FunDef] = maybeTransformer match {
           case Some(transformer) =>
             for(fd <- fundefMapping.values) {
               prevBodies += fd -> fd.body
               fd.body = fd.body.map(applySolution(solution))
             }
             val finalFunctions = fundefMapping.values.toSet
             fundefMapping get hctx.functionContext match {
               case Some(v) => finalFunctions - v
               case None => finalFunctions
             }
           case None => Set[FunDef]()
         }
         val (term, fds) = makeFunctionsUnique(assignedGuideTemplate, solutionFds)(hctx.program)
         for(fd <- fundefMapping.values) {
           fd.body = prevBodies(fd)
         }
         Solution(BooleanLiteral(true), fds, term, true)
       }
    )
  }
  
  def instantiateOn(implicit hctx: SearchContext, p: Problem): Traversable[RuleInstantiation] = {
    //hctx.reporter.debug("StringRender:Output variables="+p.xs+", their types="+p.xs.map(_.getType))
    if(hctx.currentNode.parent.nonEmpty) Nil else
    p.xs match {
      case List(IsTyped(v, StringType)) =>
        val examplesFinder = new ExamplesFinder(hctx, hctx.program)
        .setKeepAbstractExamples(true)
        .setEvaluationFailOnChoose(true)

        val examples = examplesFinder.extractFromProblem(p)
        
        val abstractStringConverters: StringConverters = p.as.flatMap { case x =>
          x.getType match {
            case FunctionType(Seq(aType), StringType) =>
              List((aType, (arg: Expr) => application(Variable(x), Seq(arg))))
            case _ => Nil
          }
        }.groupBy(_._1).mapValues(_.map(_._2))
       
        val (inputVariables, functionVariables) = p.as.partition ( x => x.getType match {
          case f: FunctionType => false
          case _ => true
        })
        
        val ruleInstantiations = ListBuffer[RuleInstantiation]()
        
        // If there is a guide, we first try to modify its string constants.
        p.wsList.collectFirst{
          case Witnesses.Guide(expr) => expr
        } match {
          case Some(guide) =>
            ruleInstantiations += RuleInstantiation("String repair") {
              repair(p, examples, guide)
            }
          case _ =>
        }
        
        
        val originalInputs = inputVariables.map(Variable)
        ruleInstantiations += RuleInstantiation("String conversion") {
          val synthesisResult = FunDefTemplateGenerator(originalInputs, functionVariables).buildFunDefTemplate(true)
          
          findSolutions(examples, synthesisResult)
        }
        
        ruleInstantiations.toList
        
      case _ => Nil
    }
  }
}
