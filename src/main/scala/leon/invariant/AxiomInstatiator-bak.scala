//package leon
//package invariant
//
//import scala.util.Random
//import z3.scala._
//import purescala.Common._
//import purescala.Definitions._
//import purescala.Trees._
//import purescala.TreeOps._
//import purescala.Extractors._
//import purescala.TypeTrees._
//import solvers.{ Solver, TimeoutSolver }
//import solvers.z3.FairZ3Solver
//import leon.evaluators._
//import java.io._
//import leon.solvers.z3.UninterpretedZ3Solver
//import leon.LeonContext
//import leon.LeonOptionDef
//import leon.LeonPhase
//import leon.LeonValueOption
//import leon.ListValue
//import leon.Reporter
//import leon.verification.DefaultTactic
//import leon.verification.ExtendedVC
//import leon.verification.Tactic
//import leon.verification.VerificationReport
//import leon.solvers.SimpleSolverAPI
//import leon.solvers.z3.UIFZ3Solver
//import leon.invariant._
//import leon.purescala.UndirectedGraph
//import scala.util.control.Breaks._
//import leon.solvers._
//import scala.concurrent._
//import scala.concurrent.duration._
//import ExecutionContext.Implicits.global
//import leon.purescala.ScalaPrinter
//import leon.plugin.NonlinearityEliminationPhase
//
//class AxiomInstantiator(ctx : LeonContext, program : Program, ctrTracker : ConstraintTracker) {              
//    
//  protected val debugAxiomInstantiation = false
//    
//  //the guards of the set of calls that were already processed
//  protected var exploredGuards = Set[Variable]()
//  //calls with axioms so far seen
//  protected var callsWithAxioms = Set[Call]() 
//  //a mapping from axioms keys (for now pairs of calls) to the guards
//  protected var axiomRoots = Map[(Call,Call),Variable]()
//   
//  def instantiate() = {
//                 
//    val funcs = ctrTracker.getFuncs        
//    funcs.foreach((fd) => {
//      val formula = ctrTracker.getVC(fd)      
//      
//      //collect the blockers of the new disjuncts
//      val disjuncts = formula.disjunctsInFormula
//      val newguards = disjuncts.keySet.diff(exploredGuards)      
//      val newCalls = newguards.flatMap(g => disjuncts(g).collect{ case c: Call => c })      
//      
////      if(this.debugAxiomInstantiation) {        
////        println("Instantianting axioms over: " + newCalls)
////        val filename = "instFormula-" + FileCountGUID.getID        
////        val wr = new PrintWriter(new File(filename + ".txt"))
////        //val printableExpr = variablesOf(formula).filterNot(TVarFactory.isTemporary _))
////        ExpressionTransformer.PrintWithIndentation(wr, simpForm)        
////        wr.flush()
////        wr.close()
////        println("Printed instFormula to file: " + filename)
////      }
//      
//      instantiateAxioms(formula, newCalls)
//      exploredGuards ++= newguards
//    })    
//  }
//  
//  //TODO: adding distributivity axiom
//   
//  def monotonizeCalls(call1: Call, call2: Call): (Seq[Expr], Expr) = {
//    if(call1.fi.funDef.id != call2.fi.funDef.id) 
//      throw IllegalStateException("Monotonizing calls to different functions: "+call1+","+call2)
//   
//    val ant = (call1.fi.args zip call2.fi.args).foldLeft(Seq[Expr]())((acc, pair) => {
//      val lesse = LessEquals(pair._1, pair._2)
//      lesse +: acc
//    })
//    val conseq = LessEquals(call1.retexpr, call2.retexpr)
//    (ant, conseq)
//  }
//   
//  /**
//   * TODO: Use least common ancestor etc. to avoid axiomatizing calls along different disjuncts
//   */
//  def instantiateAxioms(formula: Formula, calls: Set[Call]) = {
//
//    val debugSolver = if (this.debugAxiomInstantiation) {
//      val sol = new UIFZ3Solver(ctx, program)
//      sol.assertCnstr(formula.toExpr)
//      Some(sol)
//    } else None
//
//    val newCallsWithAxioms = calls.filter(call => {
//      //for now handling only monotonicity axiom
//      FunctionInfoFactory.isMonotonic(call.fi.funDef)
//    })
//
//    def isInstantiable(call1: Call, call2: Call): Boolean = {
//      //important: check if the two calls refer to the same function      
//      (call1.fi.funDef.id == call2.fi.funDef.id) && (call1 != call2)
//    }
//        
//    def cross(a : Set[Call], b: Set[Call]) : Set[(Call,Call)] = {
//      (for (x<-a; y<-b) yield (x,y)).filter(pair => isInstantiable(pair._1,pair._2))
//    } 
//      
//    val product = cross(newCallsWithAxioms,callsWithAxioms).flatMap(p => Seq((p._1,p._2),(p._2,p._1))) ++
//      cross(newCallsWithAxioms,newCallsWithAxioms).map(p => (p._1,p._2))
//    
//    //update calls with axioms
//    callsWithAxioms ++= newCallsWithAxioms
//            
//    val axiomInstances = product.foldLeft(Seq[Expr]())((acc, pair) => {      
//      val (ants, conseq) = monotonizeCalls(pair._1, pair._2)
//      val axiomInst = Implies(And(ants), conseq) 
//      
//      import ExpressionTransformer._
//      val nnfAxiom = pullAndOrs(TransformNot(axiomInst))
//      
//      val (axroot,_) = formula.conjoinWithRoot(nnfAxiom)
//      axiomRoots += (pair -> axroot)
//      
//      acc :+ axiomInst
//    })
//    
//    Stats.updateCounterStats(InvariantUtil.atomNum(And(axiomInstances)), "AxiomBlowup", "VC-refinement")
//    ctx.reporter.info("Number of axiom instances: "+axiomInstances.size)
//
//    if (this.debugAxiomInstantiation) {
//      println("Instantianting axioms over: " + newCallsWithAxioms)
//      println("Instantiated Axioms: ")
//      axiomInstances.foreach((ainst) => {
//        println(ainst)
//        debugSolver.get.assertCnstr(ainst)
//        val res = debugSolver.get.check
//        res match {
//          case Some(false) =>
//            println("adding axiom made formula unsat!!")
//          case _ => ;
//        }
//      })
//      debugSolver.get.free
//    }       
//  }
//    
//  /**
//   * Note: taking a formula as input may not be necessary. We can store it as a part of the state
//   * TODO: can we use transitivity here to optimize ?
//   */
//  def axiomsForCalls(formula: Formula, calls: Set[Call], model: Map[Identifier, Expr]): Seq[Constraint] = {    
//    (for (x<-calls; y<-calls) yield (x,y)).foldLeft(Seq[Constraint]())((acc, pair) => {      
//      val (c1,c2) = pair
//      if(c1 != c2){
//        val axRoot = axiomRoots.get(pair)
//        if (axRoot.isDefined)
//          acc ++ formula.pickSatDisjunct(axRoot.get, model)
//        else acc        
//      } else acc      
//    })
//  }
//
//}