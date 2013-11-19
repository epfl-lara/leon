package leon
package smtlib

import scala.io._
import java.io._
import SExprs._
import scala.collection._
import purescala.Trees._
import purescala.Common._
//import Trees._

object SmtlibToLeon {

  def main(args : Array[String]) {
    val  inputFilename = args(0)
    println("Parsing file : "+ inputFilename)
    val input = new BufferedReader(new InputStreamReader(new FileInputStream(args(0)))) 
    val l = new Lexer(input)
    val p = new Parser(l)   
    
    //val solver = new Z3Solver()        

    //var headers = Seq[String]()
    var symbolMap = Map[SSymbol,Expr]()
    var binderMap = Map[SSymbol,Expr]() 
    //var lambdaCtr  = 0
    //var varCtr  = 0
    var currentTree : Expr = null
    
    var expr = p.parse    
    while(expr != null) {
      
      expr match {
        case SList(List(SSymbol("SET-LOGIC"), SSymbol(logic))) => {}     
        case SList(SSymbol("SET-INFO") :: attr) => {}          
        case SList(List(SSymbol("DECLARE-SORT"), SSymbol(sort), SInt(arity))) => { }          
        case SList(List(SSymbol("DECLARE-FUN"), fun@SSymbol(fname), SList(sorts), sort)) => {
          if(!symbolMap.contains(fun)) {
/*            //if(fname.startsWith("L")) {
              symbolMap += (fun -> Lambda(lambdaCtr))
              lambdaCtr += 1
            } else {*/
              symbolMap += (fun -> Variable(FreshIdentifier(fname, true)))
              //varCtr += 1
            //}                          
          }          
        }
        case SList(List(SSymbol("ASSERT"), body)) => {
          //println(body)
          val newtree = createTree(body)          
          if(currentTree == null) currentTree = newtree
          else currentTree = And(Seq(currentTree, newtree))
          
          //solver.assertCnstr(newtree)
        }          
        case SList(List(SSymbol("CHECK-SAT"))) => { }          
        case SList(List(SSymbol("EXIT"))) => {}        
        case SList(List(SSymbol("PUSH"), SInt(n))) => { }           
        case SList(List(SSymbol("POP"), SInt(n))) => { }           
        case _ => { } 
          //throw new IllegalStateException("Unknown SExpr : "+expr)
      }

      expr = p.parse
    }
        
    def createTree(body: SExpr) : Expr = body match {
      case SList(List(SSymbol("LET"), SList(List(SList(List(binder @ SSymbol(_), value)))), body)) => {
        binderMap += (binder -> createTree(value))
        createTree(body)        
      }
      case SList(op :: args) => {        
        val exprs = args.map(createTree _)
        op match {
          case SSymbol("AND") => And(exprs)
          case SSymbol("OR") => Or(exprs)
          case SSymbol("NOT") => Not(exprs(0))
          case SSymbol("+") =>  Plus(exprs(0), exprs(1))
          case SSymbol("-") => {
            if(exprs.size == 1) UMinus(exprs(0))
            else Minus(exprs(0), exprs(1))
          } 
          case SSymbol("*") =>  Times(exprs(0), exprs(1))
          case SSymbol("=") =>  Equals(exprs(0), exprs(1))
          case SSymbol("<=") =>  LessEquals(exprs(0), exprs(1))
          case SSymbol("<") =>  LessThan(exprs(0), exprs(1))
          case SSymbol(">=") =>  GreaterEquals(exprs(0), exprs(1))
          case SSymbol(">") =>  GreaterThan(exprs(0), exprs(1))
          case _ => throw new IllegalStateException("Unknown operator: "+op)
        }               
      }      
      case s@SSymbol(idname) => {
        if(symbolMap.contains(s)) symbolMap(s)
        else if(binderMap.contains(s)) binderMap(s)
        else if(idname == "FALSE") BooleanLiteral(false)
        else if(idname == "TRUE") BooleanLiteral(true)
        else throw new IllegalStateException("Cannot find mapping for symbol: "+idname)        
      } 
      case SInt(i) => IntLiteral(i)
      case SDouble(i) => throw new IllegalStateException("Not handling doubles as of now")      
      case _ => throw new IllegalStateException("Cannot convert to tree: "+body)
    }
        
    //println("Expr: "+currentTree)
    /*val res = solver.innerCheck
    if(res == Some(true)){
      println("Found Model: "+solver.getModel)
    }*/
    
    //dump output
    LatexPrinter.dumpOutput(currentTree, args(1))    
  }
}