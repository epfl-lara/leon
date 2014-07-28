package leon
package horncl

import purescala.Trees._
import purescala.Common._
import scala.io._
import java.io._

object LatexPrinter {
  
  def dumpOutput(expr : Expr, filename : String) : Unit ={
      println("outputting to file: "+filename)
	  val output = new PrintWriter(filename)
	  //add header to the latex document	  	 	  
	  output.println("\\documentclass{article}")
	  output.println("\\usepackage{amsmath}")
	  output.println("\\begin{document}")	  	 
	  output.print("\\begin{align*} \n &")

	 //checks if 'e' is an atomic predicate without AND's and OR's
    def isAtom(e: Expr): Boolean = e match {
      case And(args) => false
      case Or(args) => false
      case _ => true
    }

    def printFormula(e: Expr): Unit = e match {
      case t : Terminal => output.print(t)
      //case Variable(id) => output.print("\\lambda_{" + id + "}")
      /*case Literal(value) => output.print(value)
      case BooleanLiteral(value) => {
        val str = if (value) "T" else "F"
        output.print(str)
      }*/
      /*case And(args) => {
        var start = true
        args.foreach((arg) => {
          if (!start) output.print("\\wedge")
          printFormula(arg)
          start = false
        })
      }
      case Or(args) => {
        var start = true
        args.foreach((arg) => {
          if (!start) output.print("\\vee")
          printFormula(arg)
          start = false
        })
      }*/
      case Not(expr) => {
        output.print("\\neg(")
        printFormula(expr)
        output.print(")")
      }
      case Plus(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print("+")
        printFormula(rhs)
        output.print(")")
      }
      case Minus(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print("-")
        printFormula(rhs)
        output.print(")")
      }
      case UMinus(expr) => {
        output.print("-(")
        printFormula(expr)
        output.print(")")
      }
      case Times(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print("*")
        printFormula(rhs)
        output.print(")")
      }
      case Equals(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print("=")
        printFormula(rhs)
        output.print(")")
      }
      case LessThan(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print("<")
        printFormula(rhs)
        output.print(")")
      }
      case GreaterThan(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print(">")
        printFormula(rhs)
        output.print(")")
      }
      case LessEquals(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print(" \\le ")
        printFormula(rhs)
        output.print(")")
      }
      case GreaterEquals(lhs, rhs) => {
        output.print("(")
        printFormula(lhs)
        output.print(" \\ge ")
        printFormula(rhs)
        output.print(")")
      }
    }

      def printRec(e: Expr, indent: Int): Unit = {
        if (isAtom(e)) printFormula(e)
        else {
          //output.println("\\\\\n" + " \\quad " * indent + "( \\\\")
          output.print("( \\\\ \n &")
          e match {
            case And(args) => {
              var start = true
              args.map((arg) => {
                output.print("  \\quad  " * (indent + 1))
                if (!start) output.print("\\wedge")
                printRec(arg, indent + 1)
                output.print("\\\\ \n &")
                start = false
              })
            }
            case Or(args) => {
              var start = true
              args.map((arg) => {
                output.print(" \\quad " * (indent + 1))
                if (!start) output.print("\\vee")
                printRec(arg, indent + 1)
                output.print("\\\\ \n&")
                start = false
              })
            }
            case _ => throw new IllegalStateException("how can this happen ? ")
          }
          output.println(" \\quad " * indent + ")")
        }
      }
      printRec(expr, 0)
      
      //add trailers
	  output.println("\\end{align*}")
	  output.println("\\end{document}")
	  output.flush()
	  output.close()
	}
}