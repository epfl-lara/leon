package test


object Example extends Unifier2[String,String] {

  implicit def str2tree(str: String): Tree = Var(str)
  def fun(str: String, trees: Tree*) = Fun(str, trees.toList)

  val t1 = fun("f", "x1", fun("g", "x2", "x3"), "x2", fun("b"))
  val t2 = fun("f", fun("g", fun("h", fun("a"), "x5"), "x2"), "x1", fun("h", fun("a"), "x4"), "x4")
	
  def main(args: Array[String]) {
  	
  	try {
  	  for ((v,t) <- unify(t1, t2))
        println("  " + v + " -> " + pp(t))
    } catch {
      case UnificationFailure(msg) =>
        println("Unification failed: " + msg)
    }
  }
}


import scala.collection.mutable.{Stack, ArrayBuffer => Seq, Map, Set}

trait Unifier2[VarName >: Null, FunName >: Null] {
 
  /* Interface */
 
  //type VarName  // <--  need type bounds :(
  //type FunName
  
  // The AST to be unified
  sealed abstract class Tree
  case class Var(name: VarName) extends Tree
  case class Fun(name: FunName, args: List[Tree]) extends Tree
  
  case class UnificationFailure(msg: String) extends Exception(msg)

  def pp(t: Tree): String = t match {
  	case Var(s) => "" + s
  	case Fun(f, ts) => "" + f + (ts map pp).mkString("(",", ",")")
  }
  
  
  def unify(tree1: Tree, tree2: Tree): Map[VarName,Tree] =
    unify(List((tree1, tree2)))
  
  def unify(trees: List[(Tree, Tree)]): Map[VarName,Tree] = {
    val variableMap = Map[VarName, Variable]()
    def convertTree(tree: Tree): Equation = tree match {
      case Var(name) => variableMap get name match {
        case Some(v) =>
          new Equation(v)
        case None =>
          val v = Variable(name)
          variableMap(name) = v
          new Equation(v)
        }
      case Fun(name, args) =>
        new Equation(Function(name, Seq(args: _*) map convertTree))
    }
    val frontier = trees map {x => merge(convertTree(x._1), convertTree(x._2))}
    val dummyVariable = new Variable(null)
    dummyVariable.eqclass.eqn.fun = Some(new Function(null, Seq(frontier: _*)))
  
    val allVariables = Seq(dummyVariable) ++ variableMap.values
    unify(allVariables map {_.eqclass})
  }
  
  /* Implementation */
  
  private case class Variable(name: VarName) {
  	var eqclass: Equivalence = new Equivalence(this) // The equivalence class for that variable
  	
  	override def toString = "" + name
  }
  private case class Function(val name: FunName, val eqns: Seq[Equation]) {
  	
  	override def toString = name + eqns.mkString("(",",",")")
  }
  private class Equation(val vars: Set[Variable] = Set(),
                         var fun: Option[Function] = None) {
                           	
  	def this(v: Variable) = this(vars = Set(v))
  	def this(f: Function) = this(fun = Some(f))
  	
  	override def toString = {
  		if (fun.isEmpty) vars.mkString("{",",","}")
  		else if (vars.isEmpty) fun.mkString
  		else vars.mkString("{",",","}") + " = " + fun.mkString
  	}
  }
  private class Equivalence(val eqn: Equation) {
  	def this(v: Variable) = this(new Equation(v))
  	var refCounter = 0
  	
  	override def toString = "[" + refCounter + "] " + eqn
  }
  
  private def unify(equivalences: Seq[Equivalence]): Map[VarName,Tree] = {
  	var numberOfClasses = equivalences.size
    val substitutions = Map[VarName,Tree]()
    val freeClasses = Stack[Equivalence]() // Equations with a zero ref counter
    
    // Initialize reference counters
    def countRefs(fun: Function) {
      for (eqn <- fun.eqns) {
      	for (v <- eqn.vars) v.eqclass.refCounter += 1
      	for (f <- eqn.fun) countRefs(f)
      }
    }
    for (equiv <- equivalences; f <- equiv.eqn.fun) countRefs(f)
    for (equiv <- equivalences; if equiv.refCounter == 0) freeClasses push equiv
    
    def compact(cl1: Equivalence, cl2: Equivalence) = {
      if (cl1 == cl2) cl1
  	  else {
  	  	numberOfClasses -= 1
  	    merge(cl1, cl2)
  	  }
    }
    
    // Main loop
    while (numberOfClasses > 0) {
      // Select multi equation
      if (freeClasses.isEmpty) {
        throw UnificationFailure("cycle")
      }
      
      val currentClass = freeClasses.pop
      val currentVars = currentClass.eqn.vars
      currentClass.eqn.fun match {
      	case Some(function) => 
          val (commonPart, frontier) = reduce(function)
          
          for (v <- currentVars)
            substitutions(v.name) = commonPart
          
          // Compact equations (i.e. merge equivalence classes)
          for (eqn <- frontier) {
   		      val eqclass = (eqn.vars map {_.eqclass}) reduceLeft compact
  		      eqclass.refCounter -= eqn.vars.size
  		      merge(eqclass.eqn, eqn)
  		      if (eqclass.refCounter == 0) freeClasses push eqclass
    		  }
        case None =>
          val representative = Var(currentVars.head.name)
          for (v <- currentVars.tail) substitutions(v.name) = representative
      }
      numberOfClasses -= 1
    }
    substitutions
  }
  
  private def merge(class1: Equivalence, class2: Equivalence): Equivalence = {
      if (class1 == class2) return class1 // should not happen !?
      if (class1.eqn.vars.size < class2.eqn.vars.size)
      	return merge(class2, class1)
      	
      merge(class1.eqn, class2.eqn)
  	  class1.refCounter += class2.refCounter
  	  for (v <- class2.eqn.vars)
  	    v.eqclass = class1
      class1
    }
  
  private def merge(equation1: Equation, equation2: Equation): Equation = {
  	if (equation1 == equation2) return equation1 // should not happen !?
  	
  	equation1.vars ++= equation2.vars
    equation1.fun match {
      case None => equation1.fun = equation2.fun
      case Some(Function(name1, args1)) => equation2.fun match {
        case Some(Function(name2, args2)) =>
          if (name1 != name2) throw UnificationFailure("clash")
          val args = for ((eqn1, eqn2) <- args1 zip args2) yield merge(eqn1, eqn2)
          equation1.fun = Some(Function(name1, args))
  	  	case None => 
  	  }
    }    
    equation1
  }
  
  private def reduce(function: Function) = {
  	val frontier = Seq[Equation]()
  	def rec(function1: Function): Tree = {
      val args = for (arg <- function1.eqns) yield {
   	    if (arg.vars.isEmpty) {
  	      rec(arg.fun.get)
  	    } else {
     	  frontier += arg
     	  Var(arg.vars.head.name)
     	}
      }
      Fun(function1.name, args.toList)
  	}
  	(rec(function), frontier)
  }
  
}