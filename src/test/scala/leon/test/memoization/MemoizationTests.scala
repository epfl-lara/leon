/* Copyright 2009-2013 EPFL, Lausanne */

package leon.test.memoization

import leon._

import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Common._
import purescala.RestoreMethods
import memoization._

import verification.AnalysisPhase

import utils.{DebugSectionMemoization}

import evaluators.{CodeGenEvaluator, EvaluationResults}
import evaluators.EvaluationResults._
import codegen.{CodeGenParams,CompilationUnit}

import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}



class MemoizationTest extends leon.test.LeonTestSuite {

 
  // Define expressions which define CaseClass expression equality correctly
  def looseTypeEq(t1 : TypeTree, t2: TypeTree) : Boolean = (t1, t2) match {
    case (BooleanType, BooleanType) | (Int32Type, Int32Type) 
       | (UnitType, UnitType) => true
    case (TupleType(tps1), TupleType(tps2)) => 
      tps1.length == tps2.length &&
      (tps1 zip tps2 forall { case (tp1, tp2) => looseTypeEq(tp1, tp2) })
    case (ListType(base1)     , ListType(base2)    ) => looseTypeEq(base1, base2)
    case (SetType(base1)      , SetType(base2)     ) => looseTypeEq(base1, base2)
    case (MultisetType(base1) , MultisetType(base2)) => looseTypeEq(base1, base2)
    case (MapType(from1, to1) , MapType(from2, to2)) => 
      looseTypeEq(from1, from2) && looseTypeEq(to1, to2)
    case (FunctionType(from1, to1), FunctionType(from2, to2)) => 
      from1.size == from2.size && 
      ( from1 zip from2 forall { case (fr1,fr2) => looseTypeEq(fr1,fr2) } ) &&
      looseTypeEq(to1, to2)
    case (ArrayType(base1)    , ArrayType(base2) )  => looseTypeEq(base1, base2)
    case (AbstractClassType(c1, _), AbstractClassType(c2, _)) => c1.id.name == c2.id.name // FIXME
    case (CaseClassType(c1, _),     CaseClassType(c2,_)) => c1.id.name == c2.id.name
    case (_, _) => false  
  }


  // equality on data structures according to name only, 
  // so as to compare structures from input and output programs
  // currently only compares constants
  // handles large test cases, so uses side effects
  def looseEq(e1: Expr, e2: Expr) : Boolean = {
    import scala.collection.mutable._
    val q = new Queue[(Expr,Expr)]()

    def localEq(e1:Expr, e2:Expr) : Boolean = (e1, e2) match { 
      case ( IntLiteral(i1), IntLiteral(i2) ) => 
        i1 == i2 
      case ( StringLiteral(s1), StringLiteral(s2) ) => 
        s1 == s2
      case ( BooleanLiteral(b1), BooleanLiteral(b2) ) =>  
        b1 == b2
      case ( UnitLiteral(), UnitLiteral() ) => 
        true
      case ( FiniteArray(exs1), FiniteArray(exs2) ) =>
        if (exs1.length != exs2.length) false 
        else { 
          exs1 zip exs2 foreach { q += _ } 
          true
        }
      case ( NilList(t1), NilList(t2) ) => 
        looseTypeEq(t1,t2)
      case ( Cons(h1, t1) , Cons(h2,t2) ) => {
        q += ((h1,h2),(t1,t2))
        true
      }
      case ( Tuple(exs1), Tuple(exs2) ) =>  
        if (exs1.length != exs2.length) false 
        else { 
          exs1 zip exs2 foreach { q += _ } ;
          true
        }
      case ( Error(_), Error(_)) => 
        true      
      case ( CaseClass(c1, args1), CaseClass(c2, args2) ) => 
        
        if (c1.id.name == c2.id.name) { 
          val l = scala.math.min(args1.length, args2.length)
          val originalFields = args1.take(l) zip args2.take(l)
          originalFields foreach { q += _ }
          true
        }
        else false  
      
      
      // FIXME : Hope that sets return items in the same order too...
      case ( f1@FiniteMap(pairs1), f2@FiniteMap(pairs2) ) => 
        if(pairs1.isEmpty && pairs2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else {
          if ( pairs1.size == pairs2.size ) { 
            pairs1 zip pairs2 foreach { case ((from1,to1), (from2,to2)) => 
              q.enqueue( (from1, from2), (to1,to2) )
            }
            true
          }
          else false 
        }

      case ( f1@FiniteSet(els1), f2@FiniteSet(els2) ) => 
        if(els1.isEmpty && els2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else { 
          if ( els1.size == els2.size ) { 
            els1 zip els2 foreach { q += _ }
            true
          } 
          else false 
        }

      case ( f1@FiniteMultiset(els1), f2@FiniteMultiset(els2) ) => 
        if(els1.isEmpty && els2.isEmpty) {
          looseTypeEq(f1.getType, f2.getType)
        } 
        else {
          if ( els1.size == els2.size ) { 
            els1 zip els2 foreach { q += _ }
            true
          } 
          else false 
        }
      case ( EmptyMultiset(t1), EmptyMultiset(t2) ) => 
        looseTypeEq(t1,t2)


      /*
      case ( Choose(vars1, pred1), Choose(vars2, preds2) ) => true // FIXME
      case ( Let(bind1, val1, bd1), Let(bind2, val2, bd2) ) => true
      case ( LetTuple(bind1, val1, bd1), LetTuple(bind2, val2, bd2) ) => true
      case ( LetDef(fd1, bd1), LetDef(fd2,bd2) ) => true
      case ( FunctionInvocation(f1, args1), FunctionInvocation(f2, args2)) => true
      case ( IfExpr(cond1, thenn1, elze1), IfExpr(cond1, thenn1, elze1)) =>
      case ( TupleSelect(tpl1, index1), TupleSelect(tpl1, index1) ) => true
      case ( MatchExpr(scr1, cases1), MatchExpr(scr2, cases2) ) => true
      case ( And(exprs1), And(exprs2) ) => 
      case ( Or(exprs1), Or(exprs2) ) => 
      case ( Iff(l1, r1), Iff(l2, r2) ) => 
      case ( Implies(l1, r1), Implies(l2, r2) ) => 
      case ( Not(
      */
      case _ => false 
    }       
    
    
    q += ((e1,e2))
    while (!q.isEmpty) {
      val (e1,e2) = q.dequeue()
      if (!localEq(e1,e2)) return false
    }
    return true

  }

  // Time a block and return time in millisec.
  def time[A]( block : => A) : (A, Double) = {
    val before = System.nanoTime
    val res    = block
    val after  = System.nanoTime 
    (res, ((after - before) *10 /1000000).toDouble * 0.1)
  }

  private def forEachFileIn(path : String)(block : File => Unit) {
    val fs = filesInResourceDir(path, _.endsWith(".scala"))

    for(f <- fs) {
      block(f)
    } 
  }

  val pipeFront = 
    frontends.scalac.ExtractionPhase andThen
    utils.PreprocessingPhase  
  val inputFilePath  = "memoization"
  val outputFilePath = "memoization"

  
  private def testMemo(f : File, how : MemoTestOptions.HowToTest) { 
    import MemoTestOptions._

    def compileTestFun(p : Program ,ctx : LeonContext) : (Expr, (Expr, Int) => EvaluationResults.Result) = {
      // We want to produce code that checks contracts
      val evaluator = new CodeGenEvaluator(ctx, p , CodeGenParams(checkContracts = true))
      how match { 
        case MemoTestOptions.Incremental => {
          // Incremental have two functions: 
          // init() : structure, which gives the initial value (Nil etc)
          // test(structure,element) : structure, which is the incremental test operation (insert etc)
          val testFun =  p.definedFunctions.find(_.id.name == "test").getOrElse {
            ctx.reporter.fatalError("Test function not defined!")
          }
          val initVal = p.definedFunctions.find(_.id.name == "init").getOrElse {
            ctx.reporter.fatalError("Initial value not defined!")
          }.body.get

          val params = testFun.params map { _.id }
          val body = testFun.body.get

          // Will apply test a number of times with the help of compileRec
          (
            initVal, evaluator.compileRec(body, params).getOrElse{
              ctx.reporter.fatalError("Failed to compile test function!")
            }
          )
        }

        case MemoTestOptions.Bulk => {
          // Bulk benchmarks have 3 functions: 
          // init() : structure , which gives the initial value (Nil etc)
          // simpleInsert(structure, element) : structure , which is the trivial insertion (e.g. cons)
          // test(structure), which is the bulk operation we will test (e.g. sort)


          val evaluator = new CodeGenEvaluator(ctx, p , CodeGenParams(checkContracts = true))
          val testFun =  p.definedFunctions.find(_.id.name == "test").getOrElse {
            ctx.reporter.fatalError("Test function not defined!")
          }
          val initVal = p.definedFunctions.find(_.id.name == "init").getOrElse {
            ctx.reporter.fatalError("Initial value not defined!")
          }.body.get
          val simpleInsert = p.definedFunctions.find(_.id.name == "simpleInsert").getOrElse {
            ctx.reporter.fatalError("simpleInsert function not defined!")
          }


          val args = simpleInsert.params map { _.id }
          val body = simpleInsert.body.get

          val construct = evaluator.compileRec(body, args).getOrElse{
            ctx.reporter.fatalError("Failed to compile simpleInsert function!")
          }
          val test = evaluator.compile(testFun.body.get, testFun.params.map{_.id}).getOrElse{
            ctx.reporter.fatalError("Failed to compile test function!")
          }

          // The complete function will construct a structure with compileRec, then apply 
          // the test operation with compile
          def complete(init: Expr, howMany : Int) : EvaluationResults.Result = 
            construct(init,howMany) match {
              case Successful(ex) => test(Seq(ex))
              case err : RuntimeError => err
              case err : EvaluatorError => err
            }

          (initVal, complete)
        }
      }
    }
    
    val outFileName = outputDirHard(outputFilePath).getAbsolutePath() ++ "/" ++ {
      how match {
        case MemoTestOptions.Incremental => "incremental"
        case MemoTestOptions.Bulk        => "bulk"
      }
    } ++ "/" ++ f.getName 
    test ("Testing " + f.getName) {
      // Compile original file
      val timeOut = 2
      val settings = testContext.settings.copy(
        memo = true, 
        debugSections = Set(DebugSectionMemoization), 
        injectLibrary = MemoTestOptions.library
      )
      val ctx = testContext.copy(
        // We want a reporter that actually prints some output
        reporter = new DefaultReporter(settings),
        settings = settings,
        options =  LeonFlagOption("fine-grain", true) +: LeonFlagOption("library", true) +: (testContext.options :+ LeonValueOption("o", outFileName) :+ LeonValueOption("timeout", timeOut.toString))
      )

      ctx.reporter.info("Now testing " + f.getAbsolutePath)
      
      val transASTWrong = if (applyTransform) { 
        ctx.reporter.info("Applying transformation")
        val pipeline = if (testWithVerify) {
          AnalysisPhase andThen 
          RemoveVerifiedPhase andThen 
          MemoizationPhase andThen
          RestoreMethods andThen
          utils.FileOutputPhase
        } else {
          MemoizationPhase andThen
          RestoreMethods andThen
          utils.FileOutputPhase
        }
        val res = (pipeFront andThen pipeline).run(ctx)(f.getAbsolutePath :: Nil)
        // Make sure you made a legal AST
        //ctx.reporter.info("Trying to compile final program to bytecode...")
        //new CompilationUnit(ctx,res,CodeGenParams(checkContracts = true)).compileModule(res.modules.head) // FIXME this has to change later
        res
      } else {
        ctx.reporter.info("Compiling transformed from source")
        val ctx1 = ctx.copy(reporter = new DefaultReporter(settings))
        pipeFront.run(ctx1)(new File(outFileName).getAbsolutePath :: Nil)
      }
      
      ctx.reporter.info("Recompiling original " + f.getName)
      
      val ctx2 = ctx.copy(reporter = new DefaultReporter(settings))
      val origAST = pipeFront.run(ctx2)(f.getAbsolutePath :: Nil) 
      
      ctx.reporter.info("Recompiling original, and removing proven FCs" + f.getName)
      val origASTRemoved = ( pipeFront andThen AnalysisPhase andThen RemoveVerifiedPhase).run(ctx2.copy())(f.getAbsolutePath()::Nil)
      
      // Test if output compiles
      if (testOutputValidity) { 
        val ctx3 = ctx.copy(reporter = new DefaultReporter(settings))
        ctx3.reporter.info("Trying to compile transformed file from source...")
        pipeFront.run(ctx3)(new File(outFileName).getAbsolutePath :: Nil) 
      }
       
      // Recompile from source to get around bugs...
      val transASTRemoved = if (applyTransform) {
        val ctx3 = ctx.copy(reporter = new DefaultReporter(settings))
        ctx3.reporter.info("Trying to compile transformed file from source...")
        pipeFront.andThen(RestoreMethods).run(ctx3)(new File(outFileName).getAbsolutePath :: Nil) 
      } else transASTWrong
      
      val transAST = {
        val ctx4 = ctx.copy(reporter = new DefaultReporter(settings), options = testContext.options :+ LeonValueOption("o", outFileName + ".2"))
        (pipeFront andThen MemoizationPhase andThen RestoreMethods andThen utils.FileOutputPhase).run(ctx4)(f.getAbsolutePath() :: Nil)
        pipeFront.andThen(RestoreMethods).run(ctx4)( new File(outFileName + ".2").getAbsolutePath() :: Nil)
      }
      
      // Compile to bytecode, check output equality and performance
      
      if (testOutputs) {

        

        ctx.reporter.info("Compiling original to bytecode")
        val (init1, compiled1) = compileTestFun(origAST,ctx)
        ctx.reporter.info("Compiling original, FCs removed to bytecode")
        val (init2, compiled2) = compileTestFun(origASTRemoved,ctx)
        ctx.reporter.info("Compiling transformed to bytecode")
        val (init3, compiled3) = compileTestFun(transAST,ctx)
        ctx.reporter.info("Compiling transformed, FCs removed to bytecode")
        val (init4, compiled4) = compileTestFun(transASTRemoved,ctx)

        val whatToRun = List(
          (testOriginal,  compiled1, init1, "        Original"),
          (testOriginalR, compiled2, init2, "    OriginalRem."),
          (testTrans,     compiled3, init3, "     Transformed"),
          (testTransR,    compiled4, init4, " TransformedRem.")
        )


        ctx.reporter.info("  Size" + (for ((true, _, _, str) <- whatToRun) yield(str)).mkString(""))

        for ((size, timesForSize) <- testSizesAndRepetitions) {
          for (i <- 1 to timesForSize) {  
            val resTimes = 
              for ( (true, compiled, init, str) <- whatToRun) yield {
                System.gc() // hopefully won't have gc in the middle of things... 
                time{compiled(init,size)}
              }
            val outAreEq = {
              val results : List[Result] = resTimes map { _._1 } 
              ( results forall { res : Result => res.isInstanceOf[RuntimeError] } ) ||
              ( results forall { res : Result => res.isInstanceOf[Successful]} ) && results.toSet.size == 1
            }
           
            var resp = ( "%5d" format size ) +
              ( resTimes map { "%14.1f" format _._2 } mkString("") ) //+
              ( if (outAreEq) "" else "  ERROR")

            ctx.reporter.info(resp)

          }
        } 
      }

    }

  }


  if (MemoTestOptions.testInc){
    forEachFileIn(inputFilePath + "/incremental") { f => 
      testMemo(f, MemoTestOptions.Incremental)
    }
  }

  if (MemoTestOptions.testPoly){
    forEachFileIn(inputFilePath + "/incrementalPoly") { f => 
      testMemo(f, MemoTestOptions.Incremental)
    }
  }
  
  if (MemoTestOptions.testBulk){
    forEachFileIn(inputFilePath + "/bulk") { f => 
      testMemo(f, MemoTestOptions.Bulk)
    }
  }

  
}
