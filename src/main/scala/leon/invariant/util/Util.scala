package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.Extractors._
import purescala.TypeTrees._
import scala.collection.mutable.{ Set => MutableSet }
import scala.collection.immutable.Stack
import java.io._
import leon.invariant._
import scala.collection.mutable.{Set => MutableSet}
import java.io._
import solvers.z3._
import solvers._

import invariant.engine._
import invariant.factories._
import invariant.structure._

object FileCountGUID {
	 var fileCount = 0
	 def getID : Int = {
	   var oldcnt = fileCount
	   fileCount += 1
	   oldcnt
	 }
}

//three valued logic
object TVL {
  abstract class Value 
  object FALSE extends Value
  object TRUE extends Value
  object MAYBE extends Value
}


//this is used as a place hold result variable if not other result variable is specified
case class ResultVariable() extends Expr with Terminal {
  override def toString : String = "#res"
}

//this used to refer to the time steps of a procedure
case class TimeVariable() extends Expr with Terminal with FixedType {
    val fixedType = Int32Type
    override def toString : String = "#time"
}

//this used to refer to the depth of a procedure
case class DepthVariable() extends Expr with Terminal with FixedType {
    val fixedType = Int32Type
    override def toString : String = "#depth"
}

object TVarFactory {
  
  val temporaries = MutableSet[Identifier]()
  //these are dummy identifiers used in 'CaseClassSelector' conversion 
  val dummyIds = MutableSet[Identifier]()
  
  def createTemp(name : String) : Identifier = {
    val freshid = FreshIdentifier(name,true)
    temporaries.add(freshid)
    freshid
  }
  
  def createDummy() : Identifier ={
    val freshid = FreshIdentifier("dy",true)
    dummyIds.add(freshid)
    freshid
  }
  
  def isTemporary(id: Identifier) : Boolean = temporaries.contains(id)
  def isDummy(id: Identifier) : Boolean = dummyIds.contains(id)  
}

object Util {
  
  val zero = IntLiteral(0)
  val one = IntLiteral(1)
  val tru = BooleanLiteral(true)
  
  /**
   * Here, we exclude empty modules without any definitions
   */
  def copyProgram(prog: Program, mapdefs: (Seq[Definition] => Seq[Definition])) : Program = {
    prog.copy(modules = prog.modules.collect {
      case module if(!module.defs.isEmpty) => module.copy(defs = mapdefs(module.defs))
    })    
  }
  
  def isNumericType(tpe: TypeTree) : Boolean = {
    tpe match {
      case  n : NumericType => true
      case _ => false
    }
  }
  
  def getFunctionReturnVariable(fd: FunDef) = {
    if(fd.hasPostcondition) fd.postcondition.get._1.toVariable
    else ResultVariable().setType(fd.returnType)
  }
  
  //compute the formal to the actual argument mapping
  def formalToAcutal(call : Call) : Map[Expr, Expr] = {
    val fd = call.fi.tfd.fd
    val resvar =getFunctionReturnVariable(fd) 
    val argmap: Map[Expr, Expr] = Map(resvar -> call.retexpr) ++ fd.params.map(_.id.toVariable).zip(call.fi.args)
    argmap
  }  
  
  /**
   * Checks if the input expression has only template variables as free variables
   */
  def isTemplateExpr(expr : Expr) :Boolean ={
    var foundVar = false    
    simplePostTransform((e : Expr) => e match {    
      case Variable(id) => { 
        if(!TemplateIdFactory.IsTemplateIdentifier(id))
          foundVar = true
        e
      }
      case ResultVariable() => {
	     foundVar = true
	     e
      }
      case _ => e
    })(expr)
    
    !foundVar
  }
  
  def getTemplateVars(expr: Expr) : Set[Variable] = {
    var tempVars = Set[Variable]()    
    simplePostTransform((e : Expr) => e match {
      case t@Variable(id) => {
        if(TemplateIdFactory.IsTemplateIdentifier(id))
        	tempVars += t
        e       
      }
      case _ => e
    })(expr)
    
    tempVars
  }

  /**
   * Checks if the expression has real valued sub-expressions.
   */
  def hasReals(expr : Expr) : Boolean = {
    var foundReal = false
    simplePostTransform((e :Expr) => e match {
      case _ => { 
        if(e.getType == RealType) 
          foundReal = true;
        e      
      }    		  	
    })(expr)
    foundReal
  }
  
  /**
   * Checks if the expression has real valued sub-expressions.
   * Note: important, <, <=, > etc have default int type.
   * However, they can also be applied over real arguments
   * So check only if all terminals are real
   */
  def hasInts(expr : Expr) : Boolean = {
    var foundInt = false
    simplePostTransform((e :Expr) => e match {
      case e : Terminal if(e.getType == Int32Type) => {              
        foundInt = true;
        e      
      } 
      case _ => e
    })(expr)
    foundInt
  }
  
  def hasMixedIntReals(expr : Expr) : Boolean = {
    hasInts(expr) && hasReals(expr)
  }
  
  
  def fix[A](f: (A) => A)(a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f)(na)
  }
  
  def atomNum(e : Expr) : Int = {
    var count : Int = 0
    simplePostTransform((e : Expr) => e match {
      case And(args) => {
        count += args.size
        e
      }         
      case Or(args) => {
        count += args.size
        e
      }
      case _ => e
    })(e)
    count
  } 
    
  def numUIFADT(e : Expr) : Int = {
    var count : Int = 0
    simplePostTransform((e : Expr) => e match {
      case FunctionInvocation(_,_) | CaseClass(_,_) | Tuple(_) => {
        count += 1
        e
      }                     
      case _ => e
    })(e)
    count
  } 
  
  def getCallExprs(ine: Expr) : Set[Expr] = {
    var calls = Set[Expr]()
    simplePostTransform((e: Expr) => e match {  
      case call @ _ if Util.isCallExpr(e) => {
        calls += e
        call
      }
      case _ => e
    })(ine)
    calls
  }
  
  def isCallExpr(e: Expr) : Boolean = e match {
    case Equals(Variable(_),FunctionInvocation(_,_)) => true
    case Iff(Variable(_),FunctionInvocation(_,_)) => true
    case _ => false
  }
  
  
  def isADTConstructor(e: Expr) : Boolean = e match {
    case Equals(Variable(_),CaseClass(_,_)) => true
    case Equals(Variable(_),Tuple(_)) => true
    case _ => false
  }
  
  
  def modelToExpr(model : Map[Identifier,Expr]) : Expr = {    
    model.foldLeft(tru : Expr)((acc, elem) => {
      val (k,v) = elem      
      val eq = Equals(k.toVariable,v)
      if(acc == tru) eq 
      else And(acc,eq)
    })
  } 

  def gcd(x: Int, y : Int) : Int ={            
    if(x == 0) y 
    else gcd(y % x, x)
  }  
  
  def toZ3SMTLIB(expr: Expr, filename: String, 
      theory: String, ctx: LeonContext, pgm: Program,
      useBitvectors : Boolean = false, 
      bitvecSize :Int = 32)  = {
    //create new solver, assert constraints and print
    val printSol = new UIFZ3Solver(ctx, pgm, useBitvectors, bitvecSize)
    printSol.assertCnstr(expr)    
    val writer = new PrintWriter(filename)
    writer.println(printSol.ctrsToString(theory))
    printSol.free()
    writer.flush()
    writer.close()
  }

  /**
   * A helper function that can be used to hardcode an invariant and see if it unsatifies the paths
   */
  def checkInvariant(expr: Expr, ctx: LeonContext, prog: Program) : Option[Boolean] = {        
    val idmap: Map[Expr, Expr] = variablesOf(expr).collect { 
      case id@_ if (id.name.toString == "a?") => id.toVariable -> IntLiteral(6)
      case id@_ if (id.name.toString == "c?") => id.toVariable -> IntLiteral(2)
      }.toMap
    //println("found ids: " + idmap.keys)
    if (!idmap.keys.isEmpty) {
      val newpathcond = replace(idmap, expr)
      //check if this is solvable
      val solver = SimpleSolverAPI(SolverFactory(() => new UIFZ3Solver(ctx, prog)))
      solver.solveSAT(newpathcond)._1 match {
        case Some(true) => {
          println("Path satisfiable for a?,c? -->6,2 ")
          Some(true)
        }
        case _ => {
          println("Path unsat for a?,c? --> 6,2")
          Some(false)
        }
      }
    } else None
  }
  
  def collectUNSATCores(ine : Expr, ctx: LeonContext, prog: Program) : Expr ={
    var controlVars = Map[Variable, Expr]()
    var newEqs = Map[Expr,Expr]()
    val solver = new UIFZ3Solver(ctx, prog)
    val newe = simplePostTransform((e: Expr) => e match {
      case And(_) | Or(_) => {
        val v = TVarFactory.createTemp("a").setType(BooleanType).toVariable
        newEqs += (v -> e)
        val newe = Equals(v, e)        
        
        //create new variable and add it in disjunction
        val cvar = FreshIdentifier("ctrl",true).setType(BooleanType).toVariable
        controlVars += (cvar -> newe)        
        solver.assertCnstr(Or(newe, cvar))
        v
      }      
      case _ => e 
    })(ine)
    //create new variable and add it in disjunction
    val cvar = FreshIdentifier("ctrl", true).setType(BooleanType).toVariable
    controlVars += (cvar -> newe)
    solver.assertCnstr(Or(newe, cvar))    
    
//    val filename = "vc-"+FileCountGUID.getID+".smt2"
//    val writer = new PrintWriter(filename)
//    writer.println(solver.ctrsToString("", unsatcore = true))    
//    writer.flush()
//    writer.close()    
//    println("Printed to file: " + filename)
    
    val res = solver.checkAssumptions(controlVars.keySet.map(Not.apply _))
    println("Result: "+res)
    val coreExprs = solver.getUnsatCore
    val simpcores = coreExprs.foldLeft(Seq[Expr]())((acc, coreExp) => {
      val Not(cvar@Variable(_)) = coreExp
      val newexp = controlVars(cvar)
      //println("newexp: "+newexp)
      newexp match {
        case Iff(v@Variable(_),rhs) if(newEqs.contains(v)) => acc
        case _ => {          
          acc :+ newexp
        }
      }      
    })
    val cores = Util.fix((e: Expr) => replace(newEqs, e))(And(simpcores.toSeq))    
    
    solver.free
    //cores
    ExpressionTransformer.unFlatten(cores,
        variablesOf(ine).filterNot(TVarFactory.isTemporary _))
  }
  
  //replaces occurrences of mult by Times
  def multToTimes(ine: Expr, ctx: InferenceContext) : Expr ={
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(fd, args) if (fd == ctx.multfun || fd == ctx.pivmultfun) => {
        Times(args(0), args(1))
      }
      case _ => e
    })(ine)
  }


  def replaceInstruVars(e: Expr, fd: FunDef): Expr = {
    //replace the time instrument variable by TimeVariable()
    val simpe = simplifyArithmetic(e)
    val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
    val withTime = if (funinfo.isDefined && funinfo.get.hasTimeexpr) {
      replace(Map(funinfo.get.getTimeexpr -> TimeVariable()), simpe)
    } else simpe

    //replace depth instrument variable by DepthVariable()    
    val withTimeAndDepth = if (funinfo.isDefined && funinfo.get.hasDepthexpr) {
      replace(Map(funinfo.get.getDepthexpr -> DepthVariable()), withTime)
    } else withTime

    //replace "res" ids by "ResultVariable"
    simplePostTransform(e => e match {
      case Variable(id) if (id.name == "res") => ResultVariable()
      case _ => e
    })(withTimeAndDepth)
  }

  /**
   * A cross product with an optional filter
   */
  def cross[U, V](a: Set[U], b: Set[V], selector: Option[(U,V) => Boolean] = None): Set[(U, V)] = {
    
    val product = (for (x <- a; y <- b) yield (x, y))
    if(selector.isDefined) 
      product.filter(pair => selector.get(pair._1,pair._2))
    else 
      product
  } 
}

/**
 * maps all real valued variables and literals to new integer variables/literals and
 * performs the reverse mapping 
 * 
 */
class RealToInt {
  
  var realToIntId = Map[Identifier, Identifier]()
  var intToRealId = Map[Identifier, Identifier]()
  
  def mapRealToInt(inexpr: Expr): Expr = {   
    val transformer = (e: Expr) => e match {
      case RealLiteral(num,1) => IntLiteral(num)
      case RealLiteral(_,_) => throw IllegalStateException("Real literal with non-unit denominator")
      case v @ Variable(realId) if (v.getType == RealType) => {
        val newId = realToIntId.getOrElse(realId, {
          val freshId = FreshIdentifier(realId.name, true).setType(Int32Type)
          realToIntId += (realId -> freshId)
          intToRealId += (freshId -> realId)
          freshId
        })
        Variable(newId)
      }      
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }
  
  def unmapModel(model: Map[Identifier, Expr]) : Map[Identifier, Expr] = {
     model.map((pair) => {
       val (key,value) = if(intToRealId.contains(pair._1)) {
         (intToRealId(pair._1),
             pair._2 match {
    		   	  case IntLiteral(v) => RealLiteral(v,1)
    		   	  case _ => pair._2
    		   	})            
       } 
       else pair
       (key -> value)
     })
  }  
}

/*class IntToReal {
    
  var intToRealDef = Map[ClassTypeDef,ClassTypeDef]() 
  var intToRealFun = Map[FunDef, FunDef]()
  var intToRealId = Map[Identifier, Identifier]()
  var realToIntId = Map[Identifier, Identifier]()

  *//**
   * Maps integer variables and constants to reals
   * Here, we assume that
   *//*
  def mapIntToReal(inexpr: Expr): Expr = {

    def intToRealClass[T <: ClassTypeDef](cdef: T): T = {
      //println("Processing Def: "+cdef)
      if (intToRealDef.contains(cdef)) {
        intToRealDef(cdef).asInstanceOf[T]
      } else {
        cdef match {
          case ccdef: CaseClassDef => 
            val newclassDef = new CaseClassDef(FreshIdentifier(ccdef.id.name,true))
            intToRealDef += (ccdef -> newclassDef)
            
            newclassDef.fields = ccdef.fields.map(vdecl => new VarDecl(vdecl.id.freshen, intToRealType(vdecl.tpe)))
            if (ccdef.hasParent){
              //println("Parent: "+ccdef.parent)
              newclassDef.setParent(intToRealClass(ccdef.parent.get))
            }
            newclassDef.asInstanceOf[T]
            
          case acdef: AbstractClassDef =>
            val newClassDef = new AbstractClassDef(FreshIdentifier(acdef.id.name,true))
            intToRealDef += (acdef -> newClassDef)
            if (acdef.hasParent) {
              //println("AbsParent: "+acdef.parent)
              newClassDef.setParent(intToRealClass(acdef.parent.get))
            }
            newClassDef.asInstanceOf[T]
        }
      }
    }

    def intToRealType(tpe: TypeTree): TypeTree = {
      //println("Processing Type: "+tpe)
      tpe match {
        case Int32Type => RealType
        case AbstractClassType(adef) => AbstractClassType(intToRealClass(adef))
        case CaseClassType(cdef) => CaseClassType(intToRealClass(cdef))
        case TupleType(bases) => TupleType(bases.map(intToRealType))
        case _ => tpe
      }
    }

    *//**
     * Assuming that the tuple-select and case-class-select have been reduced
     *//*
    def postTransformer(e: Expr): Expr = e match {
      case IntLiteral(v) => RealLiteral(v, 1)
      case v @ Variable(intId) => {
        val newtype = intToRealType(v.getType)
        if (newtype == v.getType) {
          v
        } else {
          val newId = intToRealId.getOrElse(intId, {
            val freshId = FreshIdentifier(intId.name, true).setType(newtype)
            intToRealId += (intId -> freshId)
            realToIntId += (freshId -> intId)
            freshId
          })
          Variable(newId)
        }
      }
      case FunctionInvocation(intfd, args) => {
        val newargs = args.map(postTransformer)
        val newfd = intToRealFun.getOrElse(intfd, {
          val realfd = new FunDef(FreshIdentifier(intfd.id.name,true), intToRealType(intfd.returnType),
            intfd.args.map(arg => new VarDecl(arg.id.freshen, intToRealType(arg.tpe))))
          intToRealFun += (intfd -> realfd)
          realfd
        })
        FunctionInvocation(newfd, newargs)
      }      
      case CaseClass(classDef, args) => {        
        CaseClass(intToRealClass(classDef),args.map(postTransformer))
      }
      case CaseClassInstanceOf(classDef, expr) => {
        CaseClassInstanceOf(intToRealClass(classDef),postTransformer(expr))
      }
      case t : Terminal => t
      case UnaryOperator(arg, op) => op(postTransformer(arg))
      case BinaryOperator(arg1, arg2, op) => op(postTransformer(arg1), postTransformer(arg2))
      case NAryOperator(args, op) => op(args.map(postTransformer))
    }
    val newexpr = postTransformer(inexpr)
    println("Transformed Expression: "+newexpr)
    newexpr
  }

  def unmapModel(model: Map[Identifier, Expr]): Map[Identifier, Expr] = {
    model.map((pair) => {
      val (key, value) = if (realToIntId.contains(pair._1)) {
        (realToIntId(pair._1), pair._2)
      } else pair
      (key -> value)
    })
  } 
}*/
