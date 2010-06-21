package purescala

import Common._
import Definitions._
import Trees._
import TypeTrees._
import z3.scala._
import Extensions._

class Analysis(val program: Program) {
  val extensions: Seq[Extension] = loadAll(Settings.reporter)

  if(!extensions.isEmpty) {
    Settings.reporter.info("The following extensions are loaded:\n" + extensions.toList.map(_.description).mkString("  ", ", ", ""))
  }

    // Analysis should check that:
    //  - all the postconditions are implied by preconds. + body
    //  - all callsites satisfy the preconditions
    //  - all matches are exhaustive
    // In the future:
    //  - catamorphisms are catamorphisms (poss. with surjectivity conds.)
    //  - injective functions are injective
    //  - all global invariants are satisfied 
    def analyse : Unit = {
        val z3cfg = new Z3Config()
        z3cfg.setParamValue("MODEL", "true")
        val z3 = new Z3Context(z3cfg)

        program.mainObject.defs.filter(_.isInstanceOf[FunDef]).foreach(df => {
            val funDef = df.asInstanceOf[FunDef]
            val vc = postconditionVC(funDef)
            if(vc != BooleanLiteral(true)) {
                println("Verification condition (post) for " + funDef.id + ":")
                println(vc)
                val (z3f,stupidMap) = toZ3Formula(z3, vc)
                z3.assertCnstr(z3.mkNot(z3f))
                //z3.print
                z3.checkAndGetModel() match {
                    case (Some(true),m) => {
                        println("There's a bug! Here's a model for a counter-example:")
                        m.print
                    }
                    case (Some(false),_) => println("Contract satisfied!")
                    case (None,_) => println("Z3 couldn't run properly or does not know the answer :(")
                }
            }
        }) 
    }

    def postconditionVC(functionDefinition: FunDef) : Expr = {
        val prec = functionDefinition.precondition
        val post = functionDefinition.postcondition

        if(post.isEmpty) {
            BooleanLiteral(true)
        } else {
            if(prec.isEmpty)
                replaceInExpr(Map(ResultVariable() -> functionDefinition.body), post.get)
            else
                Implies(prec.get, replaceInExpr(Map(ResultVariable() -> functionDefinition.body), post.get))
        }
    }

    def flatten(expr: Expr) : (Expr,List[(Variable,Expr)]) = {
        // Recursively flattens the expression. The head in the end
        // should be the top-level original expression.
        def fl(expr: Expr, lets: List[(Variable,Expr)]) : List[(Variable,Expr)] = expr match {
            case _ => throw new Exception("ah ha !")
        }
        
        (expr, Nil)
    }

    def replaceInExpr(substs: Map[Expr,Expr], expr: Expr) : Expr = {
        def rec(ex: Expr) : Expr = ex match {
            case _ if (substs.get(ex).isDefined) => substs(ex)
            case FunctionInvocation(fd, args) => FunctionInvocation(fd, args.map(rec(_)))
            case IfExpr(t1,t2,t3) => IfExpr(rec(t1),rec(t2),rec(t3))
            case MatchExpr(_,_) => ex
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
            case _ => ex
        }

        rec(expr)
    }

    def toZ3Formula(z3: Z3Context, expr: Expr) : (Z3AST,Map[Identifier,Z3AST]) = {
        val intSort = z3.mkIntSort()
        var varMap: Map[Identifier,Z3AST] = Map.empty

        def rec(ex: Expr) : Z3AST = ex match {
            case v @ Variable(id) => varMap.get(id) match {
                case Some(ast) => ast
                case None => {
                    assert(v.getType == Int32Type)
                    val newAST = z3.mkConst(z3.mkStringSymbol(id.name), intSort)
                    varMap = varMap + (id -> newAST)
                    newAST
                }
            } 
            case IfExpr(c,t,e) => z3.mkITE(rec(c), rec(t), rec(e))
            case And(exs) => z3.mkAnd(exs.map(rec(_)) : _*)
            case Or(exs) => z3.mkOr(exs.map(rec(_)) : _*)
            case Not(Equals(l,r)) => z3.mkDistinct(rec(l),rec(r))
            case Not(e) => z3.mkNot(rec(e))
            case Implies(l,r) => z3.mkImplies(rec(l), rec(r))
            case IntLiteral(v) => z3.mkInt(v, intSort)
            case BooleanLiteral(v) => if (v) z3.mkTrue() else z3.mkFalse()
            case Equals(l,r) => z3.mkEq(rec(l),rec(r))
            case Plus(l,r) => z3.mkAdd(rec(l), rec(r))
            case Minus(l,r) => z3.mkSub(rec(l), rec(r))
            case Times(l,r) => z3.mkMul(rec(l), rec(r))
            case Division(l,r) => z3.mkDiv(rec(l), rec(r))
            case UMinus(e) => z3.mkUnaryMinus(rec(e))
            case LessThan(l,r) => z3.mkLT(rec(l), rec(r)) 
            case LessEquals(l,r) => z3.mkLE(rec(l), rec(r)) 
            case GreaterThan(l,r) => z3.mkGT(rec(l), rec(r)) 
            case GreaterEquals(l,r) => z3.mkGE(rec(l), rec(r)) 
            case _ => scala.Predef.error("Can't handle this in translation to Z3: " + ex)
        }

        val res = rec(expr)
        (res,varMap)
    }
}
