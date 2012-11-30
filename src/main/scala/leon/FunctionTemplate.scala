package leon

import purescala.Common._
import purescala.Trees._
import purescala.Extractors._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.Definitions._

import scala.collection.mutable.{Set=>MutableSet,Map=>MutableMap}

// TODO: maybe a candidate for moving into purescala package?
class FunctionTemplate private(
  funDef : Option[FunDef],
  activatingBool : Identifier,
  condVars : Set[Identifier],
  exprVars : Set[Identifier],
  guardedExprs : Map[(Identifier,Boolean),Seq[Expr]]) {
  
  val asClauses : Seq[Expr] = {
    (for(((b,p),es) <- guardedExprs; e <- es) yield {
      Implies(if(!p) Not(Variable(b)) else Variable(b), e)
    }).toSeq
  }

  val blockers : Map[(Identifier,Boolean),Set[FunctionInvocation]] = {
    val idCall = funDef.map(fd => FunctionInvocation(fd, fd.args.map(_.toVariable)))

    Map((for((p, es) <- guardedExprs) yield {
      val calls = es.foldLeft(Set.empty[FunctionInvocation])((s,e) => s ++ functionCallsOf(e)) -- idCall
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
  def instantiate(aVar : Identifier, aPol : Boolean, args : Seq[Expr]) : (Seq[Expr],Map[(Identifier,Boolean),Set[FunctionInvocation]]) = {
    assert(this.funDef.isDefined)

    val funDef = this.funDef.get
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
    if (funDef.isDefined) {
      "Template for def " + funDef.get.id + "(" + funDef.get.args.map(a => a.id + " : " + a.tpe).mkString(", ") + ") : " + funDef.get.returnType + " is :\n"
    } else {
      "Template for expr is :\n"
    } +
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

  private val cache : MutableMap[(Option[FunDef], Option[Expr]),FunctionTemplate] = MutableMap.empty

  def mkTemplate(funDef: FunDef): FunctionTemplate =
    mkTemplate(Some(funDef), funDef.body)

  def mkTemplate(body: Expr): FunctionTemplate =
    mkTemplate(None, Some(body))

  private def mkTemplate(funDef: Option[FunDef], body : Option[Expr]) : FunctionTemplate = if(cache.isDefinedAt((funDef, body))) {
    cache((funDef, body))
  } else {
    val result = {
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
        funDef.flatMap(_.precondition.map(p => matchToIfThenElse(p)))
      } else {
        funDef.flatMap(_.precondition.map(p => matchToIfThenElse(expandLets(p))))
      }
  
      val newBody : Option[Expr] = if(KEEPLETS) {
        body.map(b => matchToIfThenElse(b))
      } else {
        body.map(b => matchToIfThenElse(expandLets(b)))
      }

      val invocation : Option[Expr] = funDef.map(fd => FunctionInvocation(fd, fd.args.map(_.toVariable)))
  
      val invocationEqualsBody : Option[Expr] = (invocation, newBody) match {
        case (Some(inv), Some(body)) =>
          val b : Expr = Equals(inv, body)

          Some(if(PREPENDPRECONDS && prec.isDefined) {
            Implies(prec.get, b)
          } else {
            b
          })

        case _ =>
          None
      }
  
      val activatingBool : Identifier = FreshIdentifier("start", true).setType(BooleanType)
  
      funDef match {
        case Some(fd) => 
          val finalPred : Option[Expr] = invocationEqualsBody.map(expr => rec(activatingBool, true, expr))
          finalPred.foreach(p => storeGuarded(activatingBool, true, p))

        case None =>
         storeGuarded(activatingBool, false, BooleanLiteral(false))
         val newFormula = rec(activatingBool, true, newBody.get)
         storeGuarded(activatingBool, true, newFormula)
      }
  
      // Now the postcondition.
      funDef match {
        case Some(fd) if fd.hasPostcondition =>
          val postHolds : Expr = {
            val post0 : Expr = if(KEEPLETS) {
              matchToIfThenElse(fd.getPostcondition)
            } else {
              matchToIfThenElse(expandLets(fd.getPostcondition))
            }
            val post : Expr = replace(Map(ResultVariable() -> invocation.get), post0)
            if(PREPENDPRECONDS && fd.hasPrecondition) {
              Implies(prec.get, post)
            } else {
              post
            }
          }
          val finalPred2 : Expr = rec(activatingBool, true, postHolds)
          storeGuarded(activatingBool, true, postHolds)
        case _ => 
          
          
      }
  
      new FunctionTemplate(funDef, activatingBool, Set(condVars.toSeq : _*), Set(exprVars.toSeq : _*), Map(guardedExprs.toSeq : _*))
    }

    cache((funDef, body)) = result
    result
  }
}
