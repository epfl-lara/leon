package leon
package invariant

import z3.scala._
import purescala.DataStructures._
import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import solvers.{ Solver, TrivialSolver, TimeoutSolver }
import solvers.z3.FairZ3Solver
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.mutable.{ Map => MutableMap }
import leon.evaluators._
import java.io._
import leon.solvers.z3.UninterpretedZ3Solver
import leon.LeonContext
import leon.LeonOptionDef
import leon.LeonPhase
import leon.LeonValueOption
import leon.ListValue
import leon.Reporter
import leon.verification.DefaultTactic
import leon.verification.ExtendedVC
import leon.verification.Tactic
import leon.verification.VerificationReport

//TODO : Critical : Implement a Real, Integer interpreter and  correctly handle conversion from real coefficients to integer coefficients
//in the model generation
class ConstraintTracker(fundef : FunDef) {

  private val implicationSolver = new LinearImplicationSolver()
  //this is a mutable map (used for efficiency)
  //private var treeNodeMap = collection.mutable.Map[Identifier, CtrNode]()
  
  //verification conditions for each procedure that may have templates.
  //Each verification condition is an implication where the antecedent and the consequent are represented as DNF trees.
  private var templatedVCs = Map[FunDef,(CtrNode,CtrNode)]()
    
  //some constants
  private val zero = IntLiteral(0)
  private val one = IntLiteral(1)
  private val mone =IntLiteral(-1)   
  private val fls = BooleanLiteral(false)
  private val tru = BooleanLiteral(true)

  //adds a constraint in conjunction with  the constraint represented by parentNode
  def addConstraintRecur(inexpr: Expr, parentNode : CtrNode) : Unit = {

    //returns a node that represents the root of the constraint
    //this is passed an end node: the node that represents the last  children of the sub-tree
    def addCtr(ie: Expr, endnode: CtrNode): CtrNode = {
      ie match {
        case Or(subexprs) => {
          val children = subexprs.foldLeft(Set[CtrNode]())((acc, sube) => {                   
            acc + addCtr(sube, endnode)
          })
          val rootnode = CtrNode()          
          children.foreach((child) => { rootnode.addChildren(child); })
          rootnode
        }
        case And(subexprs) => {
          val rootnode = subexprs.foldRight(None: Option[CtrNode])((sube, acc) => {
            val currentNode = if (acc == None) addCtr(sube, endnode)
            else addCtr(sube, acc.get)
            Some(currentNode)
          })
          rootnode.get
        }        	    
        case _ => {
          val node = CtrNode()          
          ie match {
            case Equals(v@Variable(_),fi@FunctionInvocation(_,_)) => {
            	node.uifs += Call(v,fi)
            }
            case _ => {
              val template = exprToTemplate(ie)
              if(template.isInstanceOf[LinearConstraint])
            	  node.constraints += template.asInstanceOf[LinearConstraint]
              else node.templates += template            
            } 
          }          
          node.addChildren(endnode)
          node
        }
      }
    }
    val exprRoot = addCtr(inexpr, CtrNode())
    val parentEnd = parentNode.getEndNode
    parentEnd.addChildren(exprRoot)    
  }

  def addConstraint(e: Expr, bodyRoot: CtrNode, postRoot: CtrNode, isBody: Boolean) = {
      
    val root = if(isBody) bodyRoot else postRoot    
    addConstraintRecur(e, root)           
  }

  //checks if a constraint tree exists for a function 
  def hasCtrTree(fdef: FunDef) = {
  	templatedVCs.contains(fdef)
  }

	//returns the constraint tree corresponding to a function
  def getCtrTree(fdef: FunDef) : (CtrNode,CtrNode) ={
    templatedVCs.getOrElse(fdef, {
      //initialize body and post roots
      val newentry = (CtrNode(),CtrNode())
      templatedVCs += (fdef -> newentry)
      newentry
    })    
  }

  def addBodyConstraints(fdef: FunDef, body: Expr) = {
    val (bodyRoot,postRoot) = getCtrTree(fdef)    
    addConstraint(body, bodyRoot, postRoot, true)
  }

  /**
   * This is a little tricky the post tree contains negation of the post condition.
   * This is used for optimization.  
   */
  def addPostConstraints(fdef: FunDef, npost: Expr) = {
    val (bodyRoot,postRoot) = getCtrTree(fdef)
    addConstraint(npost, bodyRoot, postRoot, false)
    //println("PostCtrTree\n"+postRoot.toString)    
  }

  /**
   * This is a little tricky. 
   * The template's negation is added in disjunction to the 
   * existing postcondition
   *//*
  def addTemplatedPostConstraints(fdef: FunDef, temp: Expr) = {
    val (_, postRoot) = getCtrTree(fdef)
    postRoot.templates += temp
    val child = CtrNode()
    child.templates += temp
    postRoot.addChildren(child)
  }*/

  /**
   * the expression 'Expr' is required to be a linear atomic predicate (or a template),
   * if not, an exception would be thrown.
   * For now some of the constructs are not handled.
   * The function returns a linear template or a linear constraint depending
   * on whether the expression has template variables or not
   */
  def exprToTemplate(expr: Expr): LinearTemplate = {
    
    //these are the result values
    var coeffMap = MutableMap[Expr, Expr]()
    var constant: Option[Expr] = None
    var isTemplate : Boolean = false

    def addCoefficient(term: Expr, coeff: Expr) = {
      if (coeffMap.contains(term)) {
        val value = coeffMap(term)        
        coeffMap.update(term, Plus(value, coeff))
      } else coeffMap += (term -> coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
    
    def addConstant(coeff: Expr) ={
      if (constant.isDefined) {
        val value = constant.get
        constant = Some(Plus(value, coeff))
      } else 
        constant = Some(coeff)

      if (!variablesOf(coeff).isEmpty) {
        isTemplate = true
      }
    }
   
    val linearExpr = MakeLinear(expr)

    //the top most operator should be a relation
    val BinaryOperator(lhs, IntLiteral(0), op) = linearExpr
    if (lhs.isInstanceOf[IntLiteral])
      throw IllegalStateException("relation on two integers, not in canonical form: " + linearExpr)

    //recurse into plus and get all minterms
    def getMinTerms(lexpr: Expr): Seq[Expr] = lexpr match {
      case Plus(e1, e2) => getMinTerms(e1) ++ getMinTerms(e2)      
      case _ => Seq(lexpr)
    }
    val minterms =  getMinTerms(lhs)

    //handle each minterm
    minterms.foreach((minterm: Expr) => minterm match {
      case _ if (InvariantUtil.isTemplateExpr(minterm)) => {
        addConstant(minterm)
      }
      case Times(e1, e2) => {
        e2 match {
          case Variable(_) => ;
          case FunctionInvocation(_, _) => ;
          case _ => throw IllegalStateException("Multiplicand not a constraint variable: " + e2)
        }
        e1 match {
          //case c @ IntLiteral(_) => addCoefficient(e2, c)
          case _ if (InvariantUtil.isTemplateExpr(e1)) => {
            addCoefficient(e2, e1)            
          }
          case _ => throw IllegalStateException("Coefficient not a constant or template expression: " + e1)
        }
      }            
      case Variable(_) => {
        //here the coefficient is 1
        addCoefficient(minterm, one)
      }
      case _ => throw IllegalStateException("Unhandled min term: " + minterm)
    })

    if(isTemplate) {
      new LinearTemplate(linearExpr, coeffMap.toMap, constant, InvariantUtil.getTemplateVars(linearExpr))
    }else{
      new LinearConstraint(linearExpr,coeffMap.toMap,constant)      
    }         
  }

  /**
   * This method may have to do all sorts of transformation to make the expressions linear constraints.
   * This assumes that the input expression is an atomic predicate (i.e, without and, or and nots)
   * This is subjected to constant modification.
   */
  def MakeLinear(atom: Expr): Expr = {

    //pushes the minus inside the arithmetic terms
    //we assume that inExpr is in linear form
    def PushMinus(inExpr: Expr): Expr = {
      require(inExpr.getType == Int32Type || inExpr.getType == RealType)

      inExpr match {
        case IntLiteral(v) => IntLiteral(-v)
        case t: Terminal => Times(mone, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mone, fi)
        case UMinus(e1) => e1
        case Minus(e1, e2) => Plus(PushMinus(e1), e2)
        case Plus(e1, e2) => Plus(PushMinus(e1), PushMinus(e2))
        case Times(e1, e2) => {
          //here push the minus in to the coefficient which is the first argument
          Times(PushMinus(e1), e2)          
        }
        case _ => throw NotImplementedException("PushMinus -- Operators not yet handled: " + inExpr)
      }
    }

    //we assume that ine is in linear form
    def PushTimes(mul: Expr, ine: Expr): Expr = {
      require((ine.getType == Int32Type || ine.getType == RealType)
          && (mul.getType == Int32Type || mul.getType == RealType))

      ine match {
        //case IntLiteral(v) => IntLiteral(c * v)
        case t: Terminal => Times(mul, t)
        case fi @ FunctionInvocation(fdef, args) => Times(mul, fi)
        case Plus(e1, e2) => Plus(PushTimes(mul, e1), PushTimes(mul, e2))
        case Times(e1, e2) => {
          //here push the times into the coefficient which should be the first expression
          Times(PushTimes(mul, e1), e2)
        }
        case _ => throw NotImplementedException("PushTimes -- Operators not yet handled: " + ine)
      }
    }

    //collect all the constants in addition and simplify them
    //we assume that ine is in linear form
    def simplifyConsts(ine: Expr): (Option[Expr], Int) = {
      require(ine.getType == Int32Type || ine.getType == RealType)

      ine match {
        case IntLiteral(v) => (None, v)
        case Plus(e1, e2) => {
          val (r1, c1) = simplifyConsts(e1)
          val (r2, c2) = simplifyConsts(e2)

          val newe = (r1, r2) match {
            case (None, None) => None
            case (Some(t), None) => Some(t)
            case (None, Some(t)) => Some(t)
            case (Some(t1), Some(t2)) => Some(Plus(t1, t2))
          }
          (newe, c1 + c2)
        }
        case _ => (Some(ine), 0)                
      }
    }

    def mkLinearRecur(inExpr: Expr): Expr = {
      inExpr match {
        case e @ BinaryOperator(e1, e2, op) 
        if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => {

          //check if the expression has real valued sub-expressions
          val isReal = InvariantUtil.hasReals(e1) || InvariantUtil.hasReals(e2) 
          val (newe, newop) = e match {
            case t: Equals => (Minus(e1, e2), op)
            case t: LessEquals => (Minus(e1, e2), LessEquals)            
            case t: GreaterEquals => (Minus(e2, e1), LessEquals)
            case t: LessThan => {
              if (isReal)
                (Minus(e1, e2), LessThan)
              else
                (Plus(Minus(e1, e2), one), LessEquals)
            }
            case t: GreaterThan => {
              if(isReal)
                 (Minus(e2,e1),LessThan)
              else 
            	 (Plus(Minus(e2, e1), one), LessEquals)	
            }
          }
          val r = mkLinearRecur(newe)
          //simplify the resulting constants
          val (Some(r2), const) = simplifyConsts(r)
          val finale = if (const != 0) Plus(r2, IntLiteral(const)) else r2
          //println(r + " simplifies to "+finale)
          newop(finale, zero)
        }
        case Minus(e1, e2) => Plus(mkLinearRecur(e1), PushMinus(mkLinearRecur(e2)))
        case UMinus(e1) => PushMinus(mkLinearRecur(e1))
        case Times(e1, e2) => {
          val (r1, r2) = (mkLinearRecur(e1), mkLinearRecur(e2))
          
          if(InvariantUtil.isTemplateExpr(r1)) {
            PushTimes(r1, r2)
          } else if(InvariantUtil.isTemplateExpr(r2)){
            PushTimes(r2, r1)
          } else 
            throw IllegalStateException("Expression not linear: " + Times(r1, r2))                     
        }
        case Plus(e1, e2) => Plus(mkLinearRecur(e1), mkLinearRecur(e2))
        case t: Terminal => t
        case fi: FunctionInvocation => fi
        /*case UnaryOperator(e,op) => op(mkLinearRecur(e))
        case BinaryOperator(e1,e2,op) => op(mkLinearRecur(e1),mkLinearRecur(e2))
        case NAryOperator(args,op) => op(args.map(mkLinearRecur(_)))*/
        case _ => throw IllegalStateException("Expression not linear: " + inExpr)
      }
    }
    val rese = mkLinearRecur(atom)
    //println("Unnormalized Linearized expression: "+unnormLinear)
    rese
  }   
    
  //some utility methods
  def getFIs(ctr: LinearConstraint): Set[FunctionInvocation] = {
    val fis = ctr.coeffMap.keys.collect((e) => e match {
      case fi: FunctionInvocation => fi
    })
    fis.toSet
  }

  /**
   * This function computes invariants belonging to the template.
   * The result is a mapping from function definitions to the corresponding invariants.
   */
  def solveForTemplates(uiSolver: UninterpretedZ3Solver): Option[Map[FunDef, Expr]] = {

    //traverse each of the functions and collect the constraints
    val nonLinearCtrs  = templatedVCs.foldLeft(Seq[Expr]())((acc, elem) => {
      val ctr = generateCtrsForTree(elem._2._1, elem._2._2, uiSolver)      
      (acc :+ ctr)
    })
    val nonLinearCtr = if(nonLinearCtrs.size == 1) nonLinearCtrs.first 
						else And(nonLinearCtrs)	

    //look for a solution of non-linear constraints. The constraint variables are all reals
    //println("Non linear constraints for this branch: " +nonLinearCtr)          
    val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
    if (res.isDefined && res.get == true) {
      //printing the model here for debugging
      //println("Model: "+model)
      //construct an invariant (and print the model)      
      val invs = templatedVCs.map((entry) => {
        
	val (fd,_) = entry
        val template = TemplateFactory.getTemplate(fd).get

	val tempvars = InvariantUtil.getTemplateVars(template)
        val tempVarMap = tempvars.map((v) => {
          //println(v.id +" mapsto " + model(v.id))
          (v,model(v.id))
        }).toMap

	//do a simple post transform and replace the template vars by their values
	val inv = simplePostTransform((tempExpr : Expr) => tempExpr match {
	    case BinaryOperator(lhs,rhs,op) 
		if ((e.isInstanceOf[Equals] || e.isInstanceOf[LessThan]
            || e.isInstanceOf[LessEquals] || e.isInstanceOf[GreaterThan]
            || e.isInstanceOf[GreaterEquals])) => { 
		
		val linearTemp = exprToTemplate(tempExpr)
                val coeffMap = linearTemp.coeffTemp.map((entry)=>{
		    val (term, coeffTemp) = entry
                    val coeff = RealValuedExprInterpreter.evaluate(replace(tempVarMap,coeffTemp))
		    (term, coeff)
		})
		val const = if(linearTemp.constTemp.isDefined) 
				Some(RealValuedExprInterpreter.evaluate(replace(tempVarMap,linearTemp.constTemp.get)))
                            else None

		val realValues = coeffMap.values.toSeq ++ if(const.isDefined) Seq(const.get) else Seq()
        
		//the coefficients could be fractions ,so collect all the denominators
		val getDenom = (t: Expr) => t match {
		  case RealLiteral(num, denum) => denum
		  case _ => 1
		}

		val denoms = realValues.foldLeft(Set[Int]())((acc, entry) => { acc + getDenom(entry) } )
		//compute the LCM of the denominators (approx. LCM)
		val lcm = denoms.foldLeft(1)((acc, d) => if (acc % d == 0) acc else acc * d)

		//scale the numerator by lcm
		val scaleNum = (t: Expr) => t match {
		  case RealLiteral(num, denum) => IntLiteral(num * (lcm / denum))
		  case IntLiteral(n) => IntLiteral(n * lcm)
		  case _ => throw IllegalStateException("Coefficient not assigned to any value")
		}
		val intCoeffMap = coeffMap.map((entry) => (entry._1, scaleNum(entry._2)))
		val intConst = if(const.isDefined) Some(scaleNum(const.get)) else None

		//create a expression
	        var invLHS = intCoeffMap.foldLeft(null: Expr)((acc, entry) => {
   		   val (term, coeff) = entry
		   val minterm = Times(coeff,term)
		   if(acc == null) minterm else Plus(acc,minterm)
	        }
	        invLHS = if(intConst.isDefined) Plus(invLHS,intConst.get) else invLHS		
		op(invLHS,zero)
  	    }
	    case _ => tempExpr
	})(template)	
	                
        (fd -> inv)
      })
      Some(invs.toMap)
    } else {
      println("Constraint Unsat: " + unsatCore)
      None
    }
  }
  
  /**
   * Returns a set of non linear constraints for the given constraint tree
   */
  def generateCtrsForTree(bodyRoot: CtrNode, postRoot : CtrNode, uiSolver : UninterpretedZ3Solver) : Expr = {       
    
    /**
     * A utility function that converts a constraint + calls into a expression.
     * Note: adds the uifs in conjunction to the ctrs
     */    
    def constraintsToExpr(ctrs: Seq[LinearConstraint], calls: Set[Call]): Expr = {
      val pathExpr = And(ctrs.foldLeft(Seq[Expr]())((acc, ctr) => (acc :+ ctr.expr)))
      val uifExpr = And(calls.map((call) => Equals(call.retexpr,call.fi)).toSeq)
      And(pathExpr, uifExpr)
    }
    
    /**
     * A helper function that creates templates for a call
     */
    var templateMap = Map[Call, Expr]()
    def templateForCall(call: Call): Expr = {

      templateMap.getOrElse(call, {
        val argmap = InvariantUtil.formalToAcutal(call, ResultVariable())
        val tempExpr = TemplateFactory.constructTemplate(argmap, call.fi.funDef)
        templateMap += (call -> tempExpr)
        tempExpr
      })
    }

    /**
     * A helper function that composes a sequence of CtrTrees using the provided operation 
     * and "AND" as the join operation
     */
    def foldAND(trees : Iterable[CtrTree], pred: CtrTree => Expr): Expr = {
      var expr: Expr = tru
      trees.foreach((tree) => {        
        if (expr != fls) {
          val res = pred(tree)
          res match {
            case BooleanLiteral(false) => expr = fls;
            case BooleanLiteral(true) => ;
            case _ => {

              if (expr == tru) {
                expr = res
              } else expr = And(expr, res)
            }
          }
        }
      })
      expr
    } 

    /**
     * The overall flow:
     * Body --pipe---> post --pipe---> templateGen --pipe---> uifConstraintGen --pipe---> endPoint
     */        
    //this tree could have 2^n paths 
    def traverseBodyTree(tree: CtrTree, currentCtrs: Seq[LinearConstraint], currentUIFs: Set[Call]): Expr = {
      tree match {
        case n @ CtrNode(_) => {
          val newCtrs = currentCtrs ++ n.constraints
          val newUIFs = currentUIFs ++ n.uifs
          //recurse into children and collect all the constraints
          foldAND(n.Children, (child : CtrTree) => traverseBodyTree(child, newCtrs, newUIFs))
        }
        case CtrLeaf() => {

          val pathexpr = constraintsToExpr(currentCtrs, currentUIFs)
          val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(pathexpr)
          if (!res.isDefined || res.get == true) {

            println("Body path expr: " + pathexpr)
            
            //pipe this to the post tree
            traversePostTree(postRoot,currentCtrs,currentUIFs,Seq(),Seq())
            
            //antSet :+= (currentCtrs.toSet,currentUIFs)                      
          } else {
            //println("Found unsat path: " + pathExpr)
            tru
          }
        }
      }
    }
     
    //this tree could have 2^n paths
    def traversePostTree(tree: CtrTree, ants: Seq[LinearConstraint], currUIFs: Set[Call],
         conseqs: Seq[LinearConstraint], currTemps: Seq[LinearTemplate]): Expr = {
    						
      tree match {
        case n @ CtrNode(_) => {          
          val newcons = conseqs ++ n.constraints
          val newuifs = currUIFs ++ n.uifs 
          val newtemps = currTemps ++ n.templates
          
          //recurse into children and collect all the constraints
          foldAND(n.Children, (child : CtrTree) => traversePostTree(child, ants, newuifs, newcons, newtemps)) 
        }
        case CtrLeaf() => {         
          //TODO: we can check here also for satisfiablility
          //pipe this to the template generation phase
          antTemplatesGen(ants, currUIFs, conseqs, currTemps)
        }
      }
    }
    
    /**
     * This adds templates for the calls in the antecedent to the path expression.
     * TODO: We are not assuming the templates of the functions called inside the templates
     */
    def antTemplatesGen(ants: Seq[LinearConstraint], calls: Set[Call],
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]) : Expr = {

      //here we consider only calls that has a ctr tree
      val templates = calls.toSeq.filter((call) => hasCtrTree(call.fi.funDef)).map(templateForCall(_))
      val root = if (!templates.isEmpty) {
        
        val ctr = And(templates)
        //println("UIF constraints: " + uifCtr)
        //flatten functions
        val nnfExpr = InvariantUtil.FlattenFunction(ctr)
        //create the root of a new  tree
        //TODO: can we reuse the old tree ??
        val newnode = CtrNode()
        //add the nnfExpr as a DNF formulae
        addConstraintRecur(nnfExpr, newnode)
        newnode
      } else CtrLeaf()
                            
      def traverseTemplateTree(tree: CtrTree, ants: Seq[LinearConstraint], antTemps : Seq[LinearTemplate],
         calls: Set[Call],
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]): Expr = {
        
        tree match {
          case n @ CtrNode(_) => {
            
            val newAnts = ants ++ n.constraints
            val newTemps = antTemps ++ n.templates
            val newCalls = calls ++ n.uifs 
            
            //recurse into children
            foldAND(n.Children, (child : CtrTree) => traverseTemplateTree(child, newAnts, newTemps, newCalls, conseqs, conseqTemps))                           
          }
          case CtrLeaf() => {            
             
            //pipe to the uif constraint generator
            uifsConstraintsGen(ants, antTemps, calls, conseqs, conseqTemps)
          }
        }
      }
      
      traverseTemplateTree(root, ants, Seq(), calls, conseqs, conseqTemps)  
    }
    
    /**
     * Eliminates the calls using the theory of uninterpreted functions
     * this could take 2^(n^2) time
     */
    def uifsConstraintsGen(ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], 
         calls: Set[Call],
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]) : Expr = {
      
      val pathexpr = constraintsToExpr(ants ++ conseqs, calls)        
      //println("All ctrs: "+ (ants ++ conseqs ++ calls ++ conseqTemps))                  
      val uifCtrs = constraintsForUIFs(calls.toSeq, pathexpr, uiSolver)
      
      val uifroot = if (!uifCtrs.isEmpty) {
      
        val uifCtr = And(uifCtrs)
        println("UIF constraints: " + uifCtr)        
        //push not inside
        val nnfExpr = InvariantUtil.TransformNot(uifCtr)        
        //create the root of the UIF tree
        //TODO: create a UIF tree once and for all and prune the paths while traversing
        val newnode = CtrNode()
        //add the nnfExpr as a DNF formulae
        addConstraintRecur(nnfExpr, newnode)
        newnode
        
      } else CtrLeaf()
      
      def traverseTree(tree: CtrTree, 
         ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate], 
         conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]): Expr = {
        
        tree match {
          case n @ CtrNode(_) => {
            val newants = ants ++ n.constraints
            //recurse into children            
            foldAND(n.Children, (child : CtrTree) => traverseTree(child, newants, antTemps, conseqs, conseqTemps))
          }
          case CtrLeaf() => {            
            //pipe to the end point that invokes the constraint solver
            endpoint(ants,antTemps,conseqs,conseqTemps)
          }
        }
      }
      
      traverseTree(uifroot, ants, antTemps, conseqs, conseqTemps)  
    }

    /**
     * Endpoint of the pipeline. Invokes the actual constraint solver.
     */
    def endpoint(ants: Seq[LinearConstraint], antTemps: Seq[LinearTemplate],
      conseqs: Seq[LinearConstraint], conseqTemps: Seq[LinearTemplate]): Expr = {
      //here we are solving A^~(B)
      if (conseqs.isEmpty && conseqTemps.isEmpty) tru
      else {
        val implCtrs = implicationSolver.constraintsForUnsat(ants, antTemps, conseqs, conseqTemps, uiSolver)
        //println("Implication Constraints: "+implCtrs)
        implCtrs
      }
    }
    
    val nonLinearCtr = traverseBodyTree(bodyRoot, Seq(), Set())

    nonLinearCtr match {
      case BooleanLiteral(true) => throw IllegalStateException("Found no constraints")
      case _ => {
        //for debugging
        /*println("NOn linear Ctr: "+nonLinearCtr)
        val (res, model, unsatCore) = uiSolver.solveSATWithFunctionCalls(nonLinearCtr)
              if(res.isDefined && res.get == true){
                println("Found solution for constraints: "+model)
              }*/
        nonLinearCtr
      }
    }    
  }

  
  //convert the theory formula into linear arithmetic formula
  //TODO: Handle ADTs also  
  def constraintsForUIFs(calls: Seq[Call], precond: Expr, uisolver: UninterpretedZ3Solver) : Seq[Expr] = {
        
    //Part(I): Finding the set of all pairs of funcs that are implied by the precond
    var impliedGraph = new UndirectedGraph[Call]()
    var nimpliedSet = Set[(Call,Call)]()
    
    //compute the cartesian product of the calls and select the pairs having the same function symbol and also implied by the precond
    val vec = calls.toArray
    val size = calls.size
    var j = 0
    val product = vec.foldLeft(Set[(Call, Call)]())((acc, call) => {

      var pairs = Set[(Call, Call)]()
      for (i <- j + 1 until size) {
        val call2 = vec(i)
        if (call.fi.funDef == call2.fi.funDef)
          pairs ++= Set((call, call2))
      }
      j += 1
      acc ++ pairs
    })
    
    product.foreach((pair) => {
      val (call1,call2) = (pair._1,pair._2)
      if(!impliedGraph.BFSReach(call1, call2)){        
        if(!nimpliedSet.contains((call1, call2))){          
          val (ant,conseqs) = axiomatizeEquality(call1,call2)
         //check if equality follows from the preconds                   
          val (nImpRes,_,_) = uisolver.solveSATWithFunctionCalls(Not(Implies(precond,ant)))
          val (impRes,_,_) = uisolver.solveSATWithFunctionCalls(And(precond,ant))
          (nImpRes,impRes) match{
            case (Some(false),_) => {
             //here the argument equality follows from the precondition
              impliedGraph.addEdge(call1, call2)              
            }
            case (_,Some(false)) => {
              //here the arg. equality will never be implied by the precond (unless the precond becomes false). 
              //Therefore we can drop this constraint           
              ;              
            }
            case _ => {
              //here the arg. equality does not follow from the precondition but may be implied by instantiation of the templates              
              nimpliedSet ++= Set((call1,call2),(call2,call1))                       
              //TODO: consider the following optimization :
              //take the model found in this case. If the instantiation of the template does not satisfy the model
              //then may be it could imply the equality. So, we could try this case later. 
            }
          }                  
        }                     
      }
    })    
    
    //Part (II) return the constraints. For each implied call, the constraints are just that their return values are equal.
    //For other calls the constraints are full implication    
    val newctrs = product.foldLeft(Seq[Expr]())((acc,pair) => {
      val (call1,call2)= pair
      if(impliedGraph.containsEdge(call1,call2)) {
        acc :+ Equals(call1.retexpr,call2.retexpr)
      }
      else if(nimpliedSet.contains(pair)) {
        val (ant,conseq) = axiomatizeEquality(call1,call2)
        acc :+ Or(Not(ant),conseq)
      }        
      else acc
    })
    newctrs
  }

  /**
   * This procedure generates constraints for the calls to be equal
   * TODO: how can we handle functions with templates variables and functions with template names
   */
  def axiomatizeEquality(call1: Call, call2: Call): (Expr, Expr) = {
    val v1 = call1.retexpr
    val fi1 = call1.fi
    val v2 = call2.retexpr
    val fi2 = call2.fi

    val ants = (fi1.args.zip(fi2.args)).foldLeft(Seq[Expr]())((acc, pair) => {
      val (arg1, arg2) = pair
      acc :+ Equals(arg1, arg2)
    })
    val conseq = Equals(v1, v2)
    (And(ants), conseq)
  } 
  
}
