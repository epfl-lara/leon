/* Copyright 2009-2014 EPFL, Lausanne */

package leon.memoization

import leon._

import utils._

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps.{functionCallsOf,preMap,preMapOnFunDef}
import purescala.TypeTrees._

import verification._


object RemoveVerifiedPhase extends LeonPhase[VerificationReport, Program] {

  // TODO: Add splitting of preconditions
  // TODO: Handle assertions
  val name = "Exclude Verified VCs phase"
  val description = "Take a verification report for a program, and remove all verified VCs from it."


  // Reporting
  private implicit val debugSection = DebugSectionMemoization
  private var ctx : LeonContext = null
  private def dbg(x:String) = ctx.reporter.debug(x)
  
  
  /**
   * Adds an extra argument to a function with a precondition,
   * and shortcuts the precondition if this is true
   */
  
  private def withExpandedPrecondition(funDef : FunDef ) = {
    
    // To the function definition itself, add an extra argument if it has precon.
    // that says if it has been verified.
    val (newArgs, newPrecon) : (Seq[ValDef], Option[Expr]) = 
      if (funDef.hasPrecondition) {
        val extraArg = FreshIdentifier("__isVerified").setType(BooleanType)
        (
          funDef.params :+ new ValDef(extraArg, BooleanType), 
          Some(Or(Variable(extraArg), funDef.precondition.get).setPos(funDef.precondition.get))
        )
      } else (funDef.params, None)


    val toRet = new FunDef(
      funDef.id, 
      funDef.tparams,
      funDef.returnType, 
      newArgs, 
      funDef.defType
    ).copiedFrom(funDef) 

    toRet.copyContentFrom(funDef)  
    toRet.precondition = newPrecon

    toRet
    
  }
  
  
  /**
   * Takes a function definition, and adds an extra boolean argument to all
   * functions with precondition
   */
  private def insertExtraArgOnFunInvocations(funDef : FunDef, isVerified : Boolean) = {
    def subst(e : Expr) : Option[Expr] = e match {
      case FunctionInvocation(tfd,args) if tfd.fd.hasPrecondition =>
        Some(FunctionInvocation(tfd, args :+ BooleanLiteral(isVerified)))
      case _ => None
    }
    preMapOnFunDef(subst,false)(funDef) // we don't want multiple substitutions -> infinite loop
  }
  
  /**
   * Takes a function that has been fed to the verifier, 
   * along with its respective verification conditions, 
   * and removes all verified pre- and postconditions from it
   */
  private def processVerified(funDef : FunDef, vcs : Seq[VerificationCondition]) : FunDef = {

    /* Postconditions */
    val postCon = funDef.postcondition
    // Separate postconditions
    val postCons : (Identifier, Seq[Expr]) = postCon match {
      case Some( (id, And(args)) ) => (id, args.sortWith{ (e1,e2) => e1.getPos < e2.getPos })
      case Some( (id, cond     ) ) => (id, Seq(cond))
      case None                    => (FreshIdentifier("_"), Seq())
    }

    // Get the postcondition VCs, make sure they are in the right order.
    // Because InductionTactic may generate multiple conditions from one expr. we have to group them
    val verifiedPostCons = vcs. filter { 
      _.kind == VCPostcondition 
    }. sortWith { 
      (vc1,vc2) => vc1.getPos < vc2.getPos 
    }. groupBy { 
      _.getPos 
    }.toSeq.sortWith { (x1,x2) => x1._1 < x2._1 }
    
    // Now keep the original unverified postCons.
    val finalPostcons = postCons._2 zip verifiedPostCons collect { 
      case (pc, (_,vpc)) if vpc exists { _.value != Some(true) } => pc
    }
    
    
    /* Preconditions */

    // Function calls of funDef with preconditions, sorted by position
    val funCalls = ( funDef.body match {
      case Some(bd) => functionCallsOf(bd).toSeq.filter { _.tfd.hasPrecondition }
      case None => Seq()
    }).sortWith { (f1, f2) => f1.getPos < f2.getPos }
    
    // Verified preconditions of funDef, sorted by position
    val verifiedPrecons = vcs.filter { 
      _.kind == VCPrecondition 
    }.sortWith { 
      (f1,f2) => f1.getPos < f2.getPos 
    }.groupBy {
      _.getPos
    }.toSeq.sortWith { (x1,x2) => x1._1 < x2._1 }
    
    /**
     * Map function invocations with preconditions to the result of their precondition verification
     */  
    val functionVerifiedStatusMap : Map[FunctionInvocation, Boolean] = ( 
      for ( (fi, pc) <- funCalls zip verifiedPrecons ) yield {
        val isVerified = pc._2 forall { _.value == Some(true)} 
        ( fi, isVerified ) 
      }
    ).toMap
 
    
    
    val toRet = withExpandedPrecondition(funDef)
    
    
    toRet.postcondition = finalPostcons.length match {
      case 0 => None 
      case 1 => Some( (postCons._1, finalPostcons.head) )
      case _ => Some( (postCons._1, And(finalPostcons)) )
    }

    // Add the extra field to all function calls with precond.
    def addExtraField(e : Expr) = e match {
      case fi@FunctionInvocation(tfd, args) if tfd.fd.hasPrecondition => {
        // By default, we consider a precond. not proven (we need this because conditions inside conditions are not checked)
        Some(FunctionInvocation(tfd, args :+ BooleanLiteral(functionVerifiedStatusMap.getOrElse(fi,false))))
      }      
      case _ => None
    }
    preMapOnFunDef(addExtraField, false) (toRet)
  
  }
  
  /**
   * Takes a function that has not been passed through the verifier,
   * adding short circuiting argument if it has precond.  
   * and marks all function invocations with precond. as unproven 
   */
  private def processNotVerified(funDef : FunDef) : FunDef = {
    val newFunDef = withExpandedPrecondition(funDef) 
    insertExtraArgOnFunInvocations(newFunDef, false)       
  }
  
  
  /**
   * Takes a function with the @verified annotation and removes all formal contracts from it
   * 
   */
  private def processWithAnnotation( funDef : FunDef ) :FunDef = {
    val newFunDef = withExpandedPrecondition(funDef) 
    newFunDef.postcondition= None
    insertExtraArgOnFunInvocations(newFunDef, true)     
  }
  
  private def excludeVerified(vRep : VerificationReport) : Program = {

    val p = vRep.program
    
    val (withAnnotation, (verified, notVerified)) = {
      val (withAnnot, withoutAnnot) = p.definedFunctions partition { _.annotations.contains("verified")}
      (withAnnot, withoutAnnot partition { vRep.fvcs.isDefinedAt(_)  } )
    }
    
     
    val readyWithAnnotation = withAnnotation map processWithAnnotation 
    val readyNotVerified    = notVerified    map processNotVerified
    val readyVerified = for ( funDef <- verified ) yield {
      processVerified( funDef, vRep.fvcs.get(funDef).get )
    }
         
    // Map old function -> new function
    val theMap = (verified ++ notVerified ++ withAnnotation)
      .zip(readyVerified ++ readyNotVerified ++ readyWithAnnotation)
      .toMap
    
    // substitutes oldfunction -> new function
    def refreshFunInvs (e : Expr) = e match {
      case FunctionInvocation(TypedFunDef(fd,tps),args) =>
        Some( FunctionInvocation(theMap.get(fd).get.typed(tps), args) )
      case _ => None 
    }
    
    // Give a copy of the original program, with the new functions
    p.duplicate.copy(modules = for (module <- p.modules) yield { 
      val newModuleFunctions = for (fun <- module.definedFunctions) yield {
        assert(theMap contains fun)
        val newFun = theMap.get(fun).get
        preMapOnFunDef(refreshFunInvs)(newFun) // 
      }
      module.copy(defs = module.defs.filterNot { _.isInstanceOf[FunDef] } ++ newModuleFunctions 
    )})

  }


  override def run(ctx: LeonContext)(vRep: VerificationReport) : Program = {
    this.ctx = ctx
    
    ctx.reporter.info(vRep.summaryString)
    ctx.reporter.info("Removing proven formal contracts...")

    val toRet = excludeVerified(vRep)
    //dbg(purescala.ScalaPrinter(toRet))
    toRet
  }


}
