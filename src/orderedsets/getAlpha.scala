package orderedsets

import purescala._
import Trees._
import Common._
import TypeTrees._
import Definitions._
import scala.collection.mutable.{Set => MutableSet}

object getAlpha {

  var program: Program = null
  def setProgram(p: Program) = program = p

  def searchAndApply(subst: Expr => Option[Expr], recursive: Boolean = true)(expr: Expr) = {
    def rec(ex: Expr, skip: Expr = null): Expr = (if(ex == skip) None else subst(ex)) match {
      case Some(newExpr) => {
          if(newExpr.getType == NoType) {
            Settings.reporter.warning("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
          }
          if(ex == newExpr)
            if(recursive) rec(ex, ex) else ex
          else
            if(recursive) rec(newExpr) else newExpr
        }
      case None => ex match {
       case l @ Let(i,e,b) => {
          val re = rec(e)
          val rb = rec(b)
          if(re != e || rb != b)
            Let(i, re, rb).setType(l.getType)
          else
            l
        }
        case f @ FunctionInvocation(fd, args) => {
          var change = false
          val rargs = args.map(a => {
            val ra = rec(a)
            if(ra != a) {
              change = true  
              ra
            } else {
              a
            }            
          })
          if(change)
            FunctionInvocation(fd, rargs).setType(f.getType)
          else
            f
        }
        case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1),rec(t2),rec(t3)).setType(i.getType)
        case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType)
        case And(exs) => And(exs.map(rec(_)))
        case Or(exs) => Or(exs.map(rec(_)))
        case Not(e) => Not(rec(e))
        case u @ UnaryOperator(t,recons) => {
          val r = rec(t)
          if(r != t)
            recons(r).setType(u.getType)
          else
            u
        }
        case b @ BinaryOperator(t1,t2,recons) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          if(r1 != t1 || r2 != t2)
            recons(r1,r2).setType(b.getType)
          else
            b
        }
        case c @ CaseClass(cd, args) => {
          CaseClass(cd, args.map(rec(_))).setType(c.getType)
        }
        case c @ CaseClassSelector(cc, sel) => {
          val rc = rec(cc)
          if(rc != cc)
            CaseClassSelector(rc, sel).setType(c.getType)
          else
            c
        }
        case _ => ex
        }
      }

    def inCase(cse: MatchCase) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  def asCatamorphism(f : FunDef) : Option[Seq[(CaseClassDef,Identifier,Seq[Identifier],Expr)]]  = {
    def recCallsOnMatchedVars(l: (CaseClassDef,Identifier,Seq[Identifier],Expr)) = {
      var varSet = MutableSet.empty[Identifier]
      searchAndApply({ case FunctionInvocation(_, Seq(Variable(id))) => varSet += id; None; case _ => None})(l._4)
      varSet.subsetOf(l._3.toSet)
    }

    val c = this.program.callees(f)
    if(f.hasImplementation && f.args.size == 1 && c.size == 1 && c.head == f) f.body.get match {
      case SimplePatternMatching(scrut, _, lstMatches) 
        if (scrut == f.args.head.toVariable) && lstMatches.forall(recCallsOnMatchedVars) => Some(lstMatches)
      case _ => None
    } else {
      None
    }
  }

  def isAlpha(varMap: Variable => Expr)(t: Expr): Option[Expr] = t match {
    case FunctionInvocation(fd, Seq(v@ Variable(_))) => asCatamorphism(fd) match {
      case None => None
      case Some(lstMatch) => varMap(v) match {
        case CaseClass(cd, args) => {
          val (_, _, ids, rhs) = lstMatch.find( _._1 == cd).get
          val repMap = Map( ids.map(id => Variable(id):Expr).zip(args):_* )
          Some(searchAndApply(repMap.get)(rhs))
        }
        case u @ Variable(_) => {
          val c = Variable(FreshIdentifier("Coll", true)).setType(t.getType)
          // TODO: Keep track of these variables for M1(t, c)
          Some(c)
        }
        case _ => error("Bad substitution")
      }
      case _ => None
    }
    case _ => None
  }

  def apply(t: Expr, varMap: Variable => Expr): Expr = {
    searchAndApply(isAlpha(varMap))(t)
  }

//  def solve(e : Expr): Option[Boolean] = {
//    searchAndApply(isAlpha(x => x))(e)
//    None
//  }
}


