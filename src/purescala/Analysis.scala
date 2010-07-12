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

  Extensions.loadAll

  val analysisExtensions: Seq[Analyser] = loadedAnalysisExtensions
  val solverExtensions: Seq[Solver] = loadedSolverExtensions

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
    // just for the summary:
    var verifiedVCs: List[(String,String,String,String)] = Nil

    solverExtensions.foreach(_.setProgram(program))

    for(funDef <- program.definedFunctions) if (Settings.functionsToAnalyse.isEmpty || Settings.functionsToAnalyse.contains(funDef.id.name)) {
      if(funDef.body.isDefined) {
        val vc = postconditionVC(funDef)
        if(vc == BooleanLiteral(false)) {
          verifiedVCs = (funDef.id.toString, "postcondition", "invalid", "trivial") :: verifiedVCs
        } else if(vc == BooleanLiteral(true)) {
          if(funDef.hasPostcondition) {
            verifiedVCs = (funDef.id.toString, "postcondition", "valid", "tautology") :: verifiedVCs
          }
        } else {
          reporter.info("Verification condition (post) for ==== " + funDef.id + " ====")
          if(Settings.unrollingLevel == 0) {
            reporter.info(simplifyLets(vc))
          } else {
            reporter.info("(not showing unrolled VCs)")
          }
          // reporter.info("Negated:")
          // reporter.info(negate(vc))
          // reporter.info("Negated, expanded:")
          // val exp = expandLets(negate(vc))
          // reporter.info(exp)

          // try all solvers until one returns a meaningful answer
          var superseeded : Set[String] = Set.empty[String]
          solverExtensions.find(se => {
            reporter.info("Trying with solver: " + se.shortDescription)
            if(superseeded(se.shortDescription) || superseeded(se.description)) {
              reporter.info("Solver was superseeded. Skipping.")
              false
            } else {
              superseeded = superseeded ++ Set(se.superseeds: _*)
              se.solve(vc) match {
                case None => false
                case Some(true) => {
                  reporter.info("==== VALID ====")
                  verifiedVCs = (funDef.id.toString, "postcondition", "valid", se.shortDescription) :: verifiedVCs
                  true
                }
                case Some(false) => {
                  reporter.error("==== INVALID ====")
                  verifiedVCs = (funDef.id.toString, "postcondition", "invalid", se.shortDescription) :: verifiedVCs
                  true
                }
              }
            }
          }) match {
            case None => {
              reporter.warning("No solver could prove or disprove the verification condition.")
              verifiedVCs = (funDef.id.toString, "postcondition", "unknown", "---") :: verifiedVCs
            }
            case _ => 
          } 
        }
      } else {
        if(funDef.postcondition.isDefined) {
          reporter.warning(funDef, "Could not verify postcondition: function implementation is unknown.")
          verifiedVCs = (funDef.id.toString, "postcondition", "unknown", "no body") :: verifiedVCs
        }
      }
    } 

    if(verifiedVCs.size > 0) {
      verifiedVCs = verifiedVCs.reverse
      val col1wdth  = verifiedVCs.map(_._1).map(_.length).max + 2
      val col2wdth  = verifiedVCs.map(_._2).map(_.length).max + 2
      val col3wdth  = verifiedVCs.map(_._3).map(_.length).max + 2
      val col4wdth  = verifiedVCs.map(_._4).map(_.length).max 
      def mk1line(line: (String,String,String,String)) : String = {
        line._1 + (" " * (col1wdth - line._1.length)) +
        line._2 + (" " * (col2wdth - line._2.length)) +
        line._3 + (" " * (col3wdth - line._3.length)) +
        line._4 
      }
      val dashes : String = "=" * (col1wdth + col2wdth + col3wdth + col4wdth)
      reporter.info("Summary:\n" + dashes + "\n" + verifiedVCs.map(mk1line(_)).mkString("\n") + "\n" + dashes)
    } else {
      reporter.info("No verification conditions were generated.")
    }
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
      val withPrec = if(prec.isEmpty) {
        bodyAndPost
      } else {
        Implies(prec.get, bodyAndPost)
      }

      import Analysis._
      // reporter.info("Before unrolling:")
      // reporter.info(expandLets(withPrec))
      val expr0 = unrollRecursiveFunctions(program, withPrec, Settings.unrollingLevel)
      // reporter.info("Before inlining:")
      // reporter.info(expandLets(expr0))
      val expr1 = inlineFunctionsAndContracts(program, expr0)
      // reporter.info("Before PM-rewriting:")
      // reporter.info(expandLets(expr1))
      val expr2 = rewriteSimplePatternMatching(expr1)
      // reporter.info("After PM-rewriting:")
      // reporter.info(expandLets(expr2))
      assert(wellOrderedLets(expr2))
      expr2
    }
  }

}

object Analysis {
  // Warning: this should only be called on a top-level formula ! It will add
  // new variables and implications in a way that preserves the validity of the
  // formula.
  def inlineFunctionsAndContracts(program: Program, expr: Expr) : Expr = {
    var extras : List[Expr] = Nil

    def applyToCall(e: Expr) : Option[Expr] = e match {
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
          extras = And(
            replace(substMap + (ResultVariable() -> newVar), fd.postcondition.get),
            Equals(newVar, FunctionInvocation(fd, fParamsAsLetVarVars).setType(fd.returnType))
          ) :: extras
          Some(mkBigLet(newVar))
          /* END CHANGE */
        } else if(fd.hasImplementation && !program.isRecursive(fd)) { // means we can inline at least one level...
          Some(mkBigLet(replace(substMap, fd.body.get)))
        } else { // we can't do much for calls to recursive functions or to functions with no bodies
          None
        }
      }
      case o => None
    }

    val finalE = searchAndReplace(applyToCall)(expr)
    val toReturn = pulloutLets(Implies(And(extras.reverse), finalE))
    toReturn
  }

  // Warning: this should only be called on a top-level formula ! It will add
  // new variables and implications in a way that preserves the validity of the
  // formula.
  def unrollRecursiveFunctions(program: Program, expression: Expr, times: Int) : Expr = {
    def unroll(exx: Expr) : (Expr,Seq[Expr]) = {
      var extras : List[Expr] = Nil

      def urf(expr: Expr, left: Int) : Expr = {
        def unrollCall(t: Int)(e: Expr) : Option[Expr] = e match {
          case f @ FunctionInvocation(fd, args) if fd.hasImplementation && program.isRecursive(fd) => {
            val newLetIDs = fd.args.map(a => FreshIdentifier(a.id.name, true).setType(a.tpe))
            val newLetVars = newLetIDs.map(Variable(_))
            val substs: Map[Expr,Expr] = Map((fd.args.map(_.toVariable) zip newLetVars) :_*)
            val bodyWithLetVars: Expr = replace(substs, fd.body.get)
            if(fd.hasPostcondition) {
              val post = fd.postcondition.get
              val newVar = Variable(FreshIdentifier("call", true)).setType(fd.returnType)
              val newExtra1 = Equals(newVar, bodyWithLetVars)
              val newExtra2 = replace(substs + (ResultVariable() -> newVar), post)
              val bigLet = (newLetIDs zip args).foldLeft(And(newExtra1, newExtra2))((e,p) => Let(p._1, p._2, e))
              extras = urf(bigLet, t-1) :: extras
              // println("*********************************")
              // println(bigLet)
              // println(" --- from -----------------------")
              // println(f)
              // println(" --- newVar is ------------------")
              // println(newVar)
              // println("*********************************")
              Some(newVar)
            } else {
              val bigLet = (newLetIDs zip args).foldLeft(bodyWithLetVars)((e,p) => Let(p._1, p._2, e))
              Some(urf(bigLet, t-1))
            }
          }
          case o => None
        }

        if(left > 0)
          searchAndReplace(unrollCall(left), false)(expr)
        else
          expr
      }
      val finalE = urf(exx, times)
      (finalE, extras)
    }

    val (savedLets, naked) = pulloutAndKeepLets(expression)
    val infoFromLets: Seq[(Expr,Seq[Expr])] = savedLets.map(_._2).map(unroll(_))
    val extrasFromLets: Seq[Expr] = infoFromLets.map(_._2).flatten
    val newLetBodies: Seq[Expr] = infoFromLets.map(_._1)
    val newSavedLets: Seq[(Identifier,Expr)] = savedLets.map(_._1) zip newLetBodies
    val (cleaned, extras) = unroll(naked)
    val toReturn = rebuildLets(newSavedLets, Implies(And(extrasFromLets ++ extras), cleaned))
    toReturn
  }

  // Rewrites pattern matching expressions where the cases simply correspond to
  // the list of constructors
  def rewriteSimplePatternMatching(expression: Expr) : Expr = {
    def rspm(expr: Expr) : (Expr,Seq[Expr]) = {
      var extras : List[Expr] = Nil

      def rewritePM(e: Expr) : Option[Expr] = e match {
        case NotSoSimplePatternMatching(_) => None
        case SimplePatternMatching(scrutinee, classType, casesInfo) => Some({
          val newVar = Variable(FreshIdentifier("pm", true)).setType(e.getType)
          val scrutAsLetID = FreshIdentifier("scrut", true).setType(scrutinee.getType)
          val lle : List[(Variable,List[Expr])] = casesInfo.map(cseInfo => {
            val (ccd, newPID, argIDs, rhs) = cseInfo
            val newPVar = Variable(newPID)
            val argVars = argIDs.map(Variable(_))
            val (rewrittenRHS, moreExtras) = rspm(rhs)
            (newPVar, List(Equals(newPVar, CaseClass(ccd, argVars)), Implies(Equals(Variable(scrutAsLetID), newPVar), Equals(newVar, rewrittenRHS))) ::: moreExtras.toList)
          }).toList
          val (newPVars, newExtras) = lle.unzip
          extras = Let(scrutAsLetID, scrutinee, And(/*Or(newPVars.map(Equals(Variable(scrutAsLetID), _))),*/BooleanLiteral(true), And(newExtras.flatten))) :: extras
          newVar
        })
        case _ => None
      }
      
      val cleanerTree = searchAndReplace(rewritePM)(expr) 
      (cleanerTree, extras.reverse)
    }
    val (savedLets, naked) = pulloutAndKeepLets(expression)
    val infoFromLets: Seq[(Expr,Seq[Expr])] = savedLets.map(_._2).map(rspm(_))
    val extrasFromLets: Seq[Expr] = infoFromLets.map(_._2).flatten
    val newLetBodies: Seq[Expr] = infoFromLets.map(_._1)
    val newSavedLets: Seq[(Identifier,Expr)] = savedLets.map(_._1) zip newLetBodies
    val (cleaned, extras) = rspm(naked)
    val toReturn = rebuildLets(newSavedLets, Implies(And(extrasFromLets ++ extras), cleaned))
    toReturn
  }
}
