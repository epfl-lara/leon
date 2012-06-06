package leon

import purescala.Common._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Definitions._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

// TODO: maybe a candidate for moving into purescala package?
class FunctionTemplate private(
  funDef : FunDef,
  activatingBool : Identifier,
  condVars : Set[Identifier],
  exprVars : Set[Identifier],
  guardedExprs : Map[(Identifier,Boolean),Seq[Expr]]) {
  
  private val asClauses : Seq[Expr] = {
    (for(((b,p),es) <- guardedExprs; e <- es) yield {
      Implies(if(!p) Not(Variable(b)) else Variable(b), e)
    }).toSeq
  }

  private val blockers : Map[(Identifier,Boolean),Set[FunctionInvocation]] = {
    val idCall = FunctionInvocation(funDef, funDef.args.map(_.toVariable))

    Map((for((p, es) <- guardedExprs) yield {
      val calls = es.foldLeft(Set.empty[FunctionInvocation])((s,e) => s ++ functionCallsOf(e)) - idCall
      if(calls.isEmpty) {
        None
      } else {
        Some((p, calls))
      }
    }).flatten.toSeq : _*)
  }
  
  // Returns two things:
  //  - a set of clauses representing the computation of the function/post
  //  - a map indicating which boolean variables guard which (recursive) fun. invoc.
  def instantiate(aVar : Identifier, aPol : Boolean, args : Seq[Expr], initialUnroll: Boolean = false) : (Seq[Expr],Map[(Identifier,Boolean),Set[FunctionInvocation]]) = {
    assert(args.size == funDef.args.size)

    val idSubstMap : Map[Identifier,Identifier] = 
      Map((for(c <- condVars) yield {
        val f = FreshIdentifier("bf", true).setType(BooleanType)
        c -> f
      }).toSeq : _*) ++
      Map((for(e <- exprVars) yield {
        val f = FreshIdentifier("ef", true).setType(e.getType)
        e -> f
      }).toSeq : _*)

    val substMap : Map[Expr,Expr] = 
      idSubstMap.map(p => Variable(p._1) -> Variable(p._2)) ++
      Map(Variable(activatingBool) -> (if(aPol) Variable(aVar) else Not(Variable(aVar)))) ++
      Map((funDef.args.map(_.toVariable) zip args) : _*) 

    (
      asClauses.map(c => replace(substMap, c)),
      blockers.map(pair => {
        val (b,p) = pair._1
        val newBP = if(b == activatingBool) {
          (aVar, p == aPol)
        } else {
          (idSubstMap(b), p)
        }
        (newBP, pair._2.map(e => replace(substMap, e).asInstanceOf[FunctionInvocation]))
      })
    )
  }

  override def toString : String = {
    "Template for def " + funDef.id + "(" + funDef.args.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + funDef.returnType + " is :\n" +
    " * Activating boolean : " + activatingBool + "\n" + 
    " * Control booleans   : " + condVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * Expression vars    : " + exprVars.toSeq.map(_.toString).mkString(", ") + "\n" +
    " * \"Clauses\"          : " + "\n    " + asClauses.mkString("\n    ") + "\n" +
    " * Block-map          : " + blockers.toString
  }
}

object FunctionTemplate {
  private val SIMPLERIFS : Boolean = true // don't clausify ite exprs. with no function calls inside
  private val PREPENDPRECONDS : Boolean = true // always instantiate axioms guarded by the precond.
  private val KEEPLETS : Boolean = true // don't expand the lets, instantiate them with the rest

  private val cache : MutableMap[FunDef,FunctionTemplate] = MutableMap.empty

  def mkTemplate(funDef : FunDef /*, program : Program*/) : FunctionTemplate = if(cache.isDefinedAt(funDef)) {
    cache(funDef)
  } else {
    val result = {
      /*
      if(!funDef.hasImplementation) {
        sys.error("Cannot create a FunctionTemplate out of a function with no body.")
      }
      */
  
      val condVars : MutableSet[Identifier] = MutableSet.empty
      val exprVars : MutableSet[Identifier] = MutableSet.empty
  
      // represents clauses of the form:
      //    (~)id => expr && ... && expr
      val guardedExprs : MutableMap[(Identifier,Boolean),Seq[Expr]] = MutableMap.empty
  
      def storeGuarded(guardVar : Identifier, guardPol : Boolean, expr : Expr) : Unit = {
        assert(expr.getType == BooleanType)
        val p : (Identifier,Boolean) = (guardVar,guardPol)
        if(guardedExprs.isDefinedAt(p)) {
          val prev : Seq[Expr] = guardedExprs(p)
          guardedExprs(p) = expr +: prev
        } else {
          guardedExprs(p) = Seq(expr)
        }
      }
  
      def rec(pathVar : Identifier, pathPol : Boolean, expr : Expr) : Expr = {
        expr match {
          case l : Let if(!KEEPLETS) => sys.error("Let's should have been eliminated.")
          case l @ Let(i, e, b) if(KEEPLETS) => {
            val newExpr : Identifier = FreshIdentifier("lt", true).setType(i.getType)
            exprVars += newExpr
            val re = rec(pathVar, pathPol, e)
            storeGuarded(pathVar, pathPol, Equals(Variable(newExpr), re))
            val rb = rec(pathVar, pathPol, replace(Map(Variable(i) -> Variable(newExpr)), b))
            rb
          }
  
          case m : MatchExpr => sys.error("MatchExpr's should have been eliminated.")
  
          case i @ IfExpr(cond, then, elze) => {
            if(SIMPLERIFS && !containsFunctionCalls(cond) && !containsFunctionCalls(then) && !containsFunctionCalls(elze)) {
              i
            } else {
              val newBool : Identifier = FreshIdentifier("b", true).setType(BooleanType)
              val newExpr : Identifier = FreshIdentifier("e", true).setType(i.getType)
              condVars += newBool
              exprVars += newExpr
              
              val crec = rec(pathVar, pathPol, cond)
              val trec = rec(newBool, true, then)
              val erec = rec(newBool, false, elze)
  
              storeGuarded(pathVar, pathPol, Iff(Variable(newBool), crec))
              storeGuarded(newBool, true,  Equals(Variable(newExpr), trec))
              storeGuarded(newBool, false, Equals(Variable(newExpr), erec))
              Variable(newExpr)
            }
          }
  
          case n @ NAryOperator(as, r) => r(as.map(a => rec(pathVar, pathPol, a))).setType(n.getType)
          case b @ BinaryOperator(a1, a2, r) => r(rec(pathVar, pathPol, a1), rec(pathVar, pathPol, a2)).setType(b.getType)
          case u @ UnaryOperator(a, r) => r(rec(pathVar, pathPol, a)).setType(u.getType)
          case t : Terminal => t
          case a : AnonymousFunction => {
            Settings.reporter.warning("AnonymousFunction literal showed up in the construction of a FunctionTemplate.")
            a
          }
        }
      }
  
      // The precondition if it exists.
      val prec : Option[Expr] = if(KEEPLETS) {
        funDef.precondition.map(p => matchToIfThenElse(p))
      } else {
        funDef.precondition.map(p => matchToIfThenElse(expandLets(p)))
      }
  
      // Treating the body first.
      /*
      val body : Expr = if(KEEPLETS) {
        matchToIfThenElse(funDef.getImplementation) 
      } else {
        matchToIfThenElse(expandLets(funDef.getImplementation))
      }
      */
      val body : Option[Expr] = if(KEEPLETS) {
        funDef.body.map(b => matchToIfThenElse(b))
      } else {
        funDef.body.map(b => matchToIfThenElse(expandLets(b)))
      }

      val invocation : Expr = FunctionInvocation(funDef, funDef.args.map(_.toVariable))
  
      /*
      val invocationEqualsBody : Expr = {
        val b : Expr = Equals(invocation, body)
        if(PREPENDPRECONDS && funDef.hasPrecondition) {
          Implies(prec.get, b)
        } else {
          b
        }
      }
      */
      val invocationEqualsBody : Option[Expr] = body.map(body => {
        val b : Expr = Equals(invocation, body)
        if(PREPENDPRECONDS && funDef.hasPrecondition) {
          Implies(prec.get, b)
        } else {
          b
        }
      })
  
      val activatingBool : Identifier = FreshIdentifier("a", true).setType(BooleanType)
  
      //val finalPred : Expr = rec(activatingBool, true, invocationEqualsBody)
      val finalPred : Option[Expr] = invocationEqualsBody.map(expr => rec(activatingBool, true, expr))
      //storeGuarded(activatingBool, true, finalPred)
      finalPred.foreach(p => storeGuarded(activatingBool, true, p))
  
      // Now the postcondition.
      if(funDef.hasPostcondition) {
        val postHolds : Expr = {
          val post0 : Expr = if(KEEPLETS) {
            matchToIfThenElse(funDef.getPostcondition)
          } else {
            matchToIfThenElse(expandLets(funDef.getPostcondition))
          }
          val post : Expr = replace(Map(ResultVariable() -> invocation), post0)
          if(PREPENDPRECONDS && funDef.hasPrecondition) {
            Implies(prec.get, post)
          } else {
            post
          }
        }
        val finalPred2 : Expr = rec(activatingBool, true, postHolds)
        storeGuarded(activatingBool, true, postHolds)
      }
  
      val ft = new FunctionTemplate(funDef, activatingBool, Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*))
      ft
    }
    cache(funDef) = result
    result
  }
}
