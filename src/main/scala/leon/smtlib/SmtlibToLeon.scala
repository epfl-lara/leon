package leon
package smtlib

import scala.io._
import java.io._
import SExprs._
import scala.collection._
import purescala.Trees._
import purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.TypeTrees._
//import Trees._

object SmtlibToLeon {

  var typemap = Map[SSymbol,TypeTree]()
  
  def main(args : Array[String]) {
    val  inputFilename = args(0)
    println("Parsing file : "+ inputFilename)
    val input = new BufferedReader(new InputStreamReader(new FileInputStream(args(0)))) 
    val l = new Lexer(input)
    val p = new Parser(l)   
    
    //val solver = new Z3Solver()        

    //var headers = Seq[String]()
    var funMap = Map[SSymbol, FunDef]()
    var symbolMap = Map[SSymbol,Expr]()
    var binderMap = Map[SSymbol,Expr]() 
    //var lambdaCtr  = 0
    //var varCtr  = 0
    var assertTrees = Seq[Expr]() 
    
    var expr = p.parse    
    while(expr != null) {
      //println("Expr: "+expr)
      expr match {
        case SList(List(SSymbol("SET-LOGIC"), SSymbol(logic))) => {}
        case SList(SSymbol("SET-INFO") :: attr) => {}
        case SList(List(SSymbol("DECLARE-SORT"), SSymbol(sort), SInt(arity))) => {}
        case SList(List(SSymbol("DECLARE-DATATYPES"), empty, SList(body))) => {
          body.foreach((adtdec) => adtdec match {
            case SList(abs :: subtypes) if abs.isInstanceOf[SSymbol] => {
              
              //create a new abstract type, here 
              val abstype = AbstractClassType(new AbstractClassDef(FreshIdentifier(abs.asInstanceOf[SSymbol].s, false)))
              typemap += (abs.asInstanceOf[SSymbol] -> abstype) 
              
              subtypes.foreach((dtdec) => dtdec match {
                case SList(List(sym @ SSymbol(name))) => {
                  //create a new case class type here
                  val clstype = CaseClassType(new CaseClassDef(FreshIdentifier(name, false),Some(abstype.classDef)))
                  typemap += (sym -> clstype)
                  
                  //create a case class constructor function with zero arguments
                  val ccCons = new FunDef(FreshIdentifier(sym.s, false), abstype,Seq())
                  funMap += (sym -> ccCons)
                }
                case SList(head :: fields) if head.isInstanceOf[SSymbol] => {
                  
                  val clssym = head.asInstanceOf[SSymbol]
                  //create a new case class type here
                  val clstype = CaseClassType(new CaseClassDef(
                      FreshIdentifier(clssym.s, false),
                      Some(abstype.classDef)
                      ))
                  typemap += (clssym -> clstype)
                  
                  var fieldTypes = Seq[TypeTree]()
                  //fields are converted to functions
                  fields.foreach((field) => field match {
                    case SList(List(fsym@SSymbol(_), ftype@SSymbol(_))) => {
                       if(!funMap.contains(fsym)){
                         val rettype = getType(ftype)                         
                         val argDecls = Seq(VarDecl(FreshIdentifier("arg",true).setType(abstype), abstype))
                         val fd = new FunDef(FreshIdentifier(fsym.s, false), rettype,  argDecls) 
                         funMap += (fsym -> fd)
                                                  
                         fieldTypes :+= rettype
                       }                      
                    }
                    case _ => throw new IllegalStateException("Field declaration malformed")
                  })
                  
                  //create a case class constructor function
                  val ccCons = new FunDef(FreshIdentifier(clssym.s, false), abstype, 
                		  					fieldTypes.map((ft) => VarDecl(FreshIdentifier("fld",true).setType(ft), ft)))
                  funMap += (clssym -> ccCons)
                }
                case _ => throw new IllegalStateException("Subtype declaration malformed")
              })
            }
            case _ => throw new IllegalStateException("abstract type declaration malformed")
          })

          //consider each field a function  
        }
        case SList(List(SSymbol("DECLARE-FUN"), fun@SSymbol(fname), SList(sorts), rsort)) => {
          if(!funMap.contains(fun)) {
/*            //if(fname.startsWith("L")) {
              symbolMap += (fun -> Lambda(lambdaCtr))
              lambdaCtr += 1
            } else {*/
            //create a function
            val funid = FreshIdentifier(fname, true)
            val rettype = getType(rsort.asInstanceOf[SSymbol])
            val argdecls = sorts.map((argtype) => {
              val tpe = getType(argtype.asInstanceOf[SSymbol])
              val argid = FreshIdentifier("arg",true).setType(tpe)
              VarDecl(argid, tpe)              
            })                                    
            val fundef = new FunDef(funid, rettype, argdecls)
            funMap += (fun -> fundef)
              //varCtr += 1
            //}                          
          }          
        }
        case SList(List(SSymbol("ASSERT"), body)) => {
          //println(body)                
          assertTrees :+= createTree(body)                              
          //solver.assertCnstr(newtree)
        }          
        case SList(List(SSymbol("CHECK-SAT"))) => { 
        }
        case SList(SSymbol("CHECK-SAT-USING") :: _) => { 
        }          
        case SList(List(SSymbol("EXIT"))) => {}        
        case SList(List(SSymbol("PUSH"), SInt(n))) => { }           
        case SList(List(SSymbol("POP"), SInt(n))) => { }        
        case _ => 
          throw new IllegalStateException("Unknown SExpr : "+expr)
      }      
      expr = p.parse      
    }

    def createTree(body: SExpr): Expr = {
      //println("SEXPR: " + body)      
      body match {
        case SList(List(SSymbol("FORALL"), SList(boundvars), body)) => {
          //create a mapping from symbols to variables
          boundvars.foreach((pair) => {
            val SList(List(sym @ SSymbol(symname), sort)) = pair
            if (!symbolMap.contains(sym)) {
              val tpe = getType(sort.asInstanceOf[SSymbol])
              val varid = FreshIdentifier(symname, true).setType(tpe)                             
              symbolMap += (sym -> Variable(varid))
            }
          })
          createTree(body)
        }
        case SList(List(SSymbol("LET"), SList(List(SList(List(binder @ SSymbol(_), value)))), body)) => {
          binderMap += (binder -> createTree(value))
          createTree(body)
        }
        case SList(op :: args) => {
          val exprs = args.map(createTree _)
          op match {
            case SSymbol("ITE") => IfExpr(exprs(0), exprs(1), exprs(2))
            case SSymbol("AND") => And(exprs)
            case SSymbol("OR") => Or(exprs)
            case SSymbol("NOT") => Not(exprs(0))
            case SSymbol("=>") => Implies(exprs(0), exprs(1))
            case SSymbol("+") => Plus(exprs(0), exprs(1))
            case SSymbol("-") => {
              if (exprs.size == 1) UMinus(exprs(0))
              else Minus(exprs(0), exprs(1))
            }
            case SSymbol("*") => Times(exprs(0), exprs(1))
            case SSymbol("=") => Equals(exprs(0), exprs(1))
            case SSymbol("<=") => LessEquals(exprs(0), exprs(1))
            case SSymbol("<") => LessThan(exprs(0), exprs(1))
            case SSymbol(">=") => GreaterEquals(exprs(0), exprs(1))
            case SSymbol(">") => GreaterThan(exprs(0), exprs(1))
            case sym@SSymbol(_) if(funMap.contains(sym)) => FunctionInvocation(funMap(sym), exprs)
            case SSymbol(str) if(str.startsWith("IS-")) => {
              val typename = str.substring(3)
              val cct = getType(SSymbol(typename)).asInstanceOf[CaseClassType]              
              CaseClassInstanceOf(cct.classDef, exprs(0))
            }            
            case _ => throw new IllegalStateException("Unknown operator: " + op)
          }
        }
        case s @ SSymbol(idname) => {
          if (symbolMap.contains(s)) symbolMap(s)
          else if (binderMap.contains(s)) binderMap(s)
          else if (idname == "FALSE") BooleanLiteral(false)
          else if (idname == "TRUE") BooleanLiteral(true)          
          else if (idname.startsWith("-")) IntLiteral(idname.toInt)
          else if (funMap.contains(s)) FunctionInvocation(funMap(s), Seq()) //this could be a constant function
          else throw new IllegalStateException("Cannot find mapping for symbol: " + idname)
        }
        case SInt(i) => IntLiteral(i.toInt)
        case SDouble(i) => throw new IllegalStateException("Not handling doubles as of now")
        case _ => throw new IllegalStateException("Cannot convert to tree: " + body)
      }
    }
        
    println("Horn Clauses: ")
    println(assertTrees.map(_.toString).mkString("\n"))
    /*val res = solver.innerCheck
    if(res == Some(true)){
      println("Found Model: "+solver.getModel)
    }*/
    
    //dump output
    //LatexPrinter.dumpOutput(currentTree, args(1))    
  }
    
  def getType(sym : SSymbol) : TypeTree = {
    sym.s match {
      case "INT" => Int32Type
      case "BOOL" => BooleanType
      case "DOUBLE" => RealType
      case _  if(typemap.contains(sym)) => typemap(sym)
      case _ => throw IllegalStateException("Type not supported: "+sym)
    }
  }
}