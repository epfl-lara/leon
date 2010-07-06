package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._
import Extensions._

class Analysis(val program: Program) {
  // we always use the global reporter for this class
  val reporter = Settings.reporter
  // ...but not always for the extensions
  val extensionsReporter =
    if(Settings.quietExtensions) {
      Settings.quietReporter
    } else {
      Settings.reporter
    }

  // these extensions are always loaded, unless specified otherwise
  val defaultExtensions: Seq[Extension] =
    if(Settings.runDefaultExtensions) {
      (new Z3Solver(extensionsReporter)) :: Nil
    } else {
      Nil
    }

  // we load additional extensions
  val moreExtensions: Seq[Extension] = loadAll(extensionsReporter)
  if(!moreExtensions.isEmpty) {
    reporter.info("The following extensions are loaded:\n" + moreExtensions.toList.map(_.description).mkString("  ", "\n  ", ""))
  }
  // ...and split the final list between solvers and analysers
  val extensions: Seq[Extension] = defaultExtensions ++ moreExtensions
  val analysisExtensions: Seq[Analyser] = extensions.filter(_.isInstanceOf[Analyser]).map(_.asInstanceOf[Analyser])
  val solverExtensions: Seq[Solver] = extensions.filter(_.isInstanceOf[Solver]).map(_.asInstanceOf[Solver])

  // Calling this method will run all analyses on the program passed at
  // construction time. If at least one solver is loaded, verification
  // conditions are generated and passed to all solvers. Otherwise, only the
  // Analysis extensions are run on the program.
  def analyse : Unit = {
    if(solverExtensions.size > 0) {
      reporter.info("Running verification condition generation...")
      checkVerificationConditions
    } 

    analysisExtensions.foreach(ae => {
      reporter.info("Running analysis from extension: " + ae.description)
      ae.analyse(program)
    })
  }

  def checkVerificationConditions : Unit = {
    solverExtensions.foreach(_.setProgram(program))

    // Analysis should check that:
    //  - all the postconditions are implied by preconds. + body
    //  - all callsites satisfy the preconditions
    //  - all matches are exhaustive
    // In the future:
    //  - catamorphisms are catamorphisms (poss. with surjectivity conds.)
    //  - injective functions are injective
    //  - all global invariants are satisfied 
    program.mainObject.defs.filter(_.isInstanceOf[FunDef]).foreach(df => {
      val funDef = df.asInstanceOf[FunDef]

      if(funDef.body.isDefined) {
        // val vc = postconditionVC(funDef)
        // slightly more costly:
        val vc = simplifyLets(postconditionVC(funDef))
        if(vc != BooleanLiteral(true)) {
          reporter.info("Verification condition (post) for " + funDef.id + ":")
          reporter.info(vc)
          // reporter.info("Negated:")
          // reporter.info(negate(vc))
          reporter.info("Negated, expanded:")
          reporter.info(expandLets(negate(vc)))

          // try all solvers until one returns a meaningful answer
          solverExtensions.find(se => {
            reporter.info("Trying with solver: " + se.shortDescription)
            se.solve(vc) match {
              case None => false
              case Some(true) => reporter.info("_,.-~*' VALID '*~-.,_"); true
              case Some(false) => reporter.error("_,.-~*' INVALID '*~-.,_"); true
            }
          }) match {
            case None => reporter.warning("No solver could prove or disprove the verification condition.")
            case _ => 
          } 
        }
      } else {
        if(funDef.postcondition.isDefined) {
          reporter.warning(funDef, "Could not verify postcondition: function implementation is unknown.")
        }
      }
    }) 
  }

  def postconditionVC(functionDefinition: FunDef) : Expr = {
    assert(functionDefinition.body.isDefined)
    val prec = functionDefinition.precondition
    val post = functionDefinition.postcondition
    val body = functionDefinition.body.get

    if(post.isEmpty) {
      BooleanLiteral(true)
    } else {
      val resFresh = FreshIdentifier("result", true).setType(body.getType)
      val bodyAndPost = Let(resFresh, body, replace(Map(ResultVariable() -> Variable(resFresh)), post.get))
      val beforeInlining = if(prec.isEmpty) {
        bodyAndPost
      } else {
        Implies(prec.get, bodyAndPost)
      }

      val (newExpr, sideExprs) = inlineFunctionsAndContracts(beforeInlining)

      if(sideExprs.isEmpty) {
        newExpr
      } else {
        Implies(And(sideExprs), newExpr)
      }
    }
  }

  def inlineFunctionsAndContracts(expr: Expr) : (Expr, Seq[Expr]) = {
    var extras : List[Expr] = Nil

    val isFunCall: Function[Expr,Boolean] = _.isInstanceOf[FunctionInvocation]
    def applyToCall(e: Expr) : Expr = e match {
      case f @ FunctionInvocation(fd, args) => {
        val fArgsAsVars: List[Variable] = fd.args.map(_.toVariable).toList
        val fParamsAsLetVars: List[Identifier] = fd.args.map(a => FreshIdentifier("arg", true).setType(a.tpe)).toList
        val fParamsAsLetVarVars = fParamsAsLetVars.map(Variable(_))
  
        def mkBigLet(ex: Expr) : Expr = (fParamsAsLetVars zip args).foldRight(ex)((iap, e) => {
          Let(iap._1, iap._2, e)
        })

        val substMap = Map[Expr,Expr]((fArgsAsVars zip fParamsAsLetVarVars) : _*)
        if(fd.hasPostcondition) {
          val newVar = Variable(FreshIdentifier("call", true)).setType(fd.returnType)
          extras = mkBigLet(And(
            replace(substMap + (ResultVariable() -> newVar), fd.postcondition.get),
            Equals(newVar, FunctionInvocation(fd, fParamsAsLetVarVars).setType(fd.returnType))
          )) :: extras
          newVar
        } else if(fd.hasImplementation && !program.isRecursive(fd)) { // means we can inline at least one level...
          mkBigLet(replace(substMap, fd.body.get))
        } else { // we can't do much for calls to recursive functions or to functions with no bodies
          f 
        }
      }
      case o => o
    }

    (searchAndApply(isFunCall, applyToCall, expr), extras.reverse)
  }

  def rewritePatternMatching(expr: Expr) : (Expr, Seq[Expr]) = {
    var nodeCount: Int = 0
    def newNode : Node = {
      val ret = Node(nodeCount)
      nodeCount = nodeCount + 1
      ret
    }
    sealed abstract class PatternGraph
    case class Node(id: Int) extends PatternGraph

    var extras : List[Expr] = Nil

    def isPMExpr(e: Expr) : Boolean = e.isInstanceOf[MatchExpr]

    def rewritePM(e: Expr) : Expr = e match {
      case m @ MatchExpr(_, _) => {

        m
      }
      case o => o
    }

    (searchAndApply(isPMExpr, rewritePM, expr), extras.reverse)
  }
}
