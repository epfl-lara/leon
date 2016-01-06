package leon
package synthesis.disambiguation

import synthesis.RuleClosed
import synthesis.Solution
import evaluators.DefaultEvaluator
import purescala.Expressions._
import purescala.ExprOps
import purescala.Constructors._
import purescala.Extractors._
import purescala.Types.{TypeTree, TupleType, BooleanType}
import purescala.Common.Identifier
import purescala.Definitions.{FunDef, Program}
import purescala.DefOps
import grammars.ValueGrammar
import bonsai.enumerators.MemoizedEnumerator
import solvers.Model
import solvers.ModelBuilder
import scala.collection.mutable.ListBuffer

import leon.LeonContext

/**
 * @author Mikael
 * If possible, synthesizes a set of inputs for the function so that they cover all parts of the function.
 * 
 * @param fds The set of functions to cover
 * @param fd The calling function
 */
class InputCoverage(fd: FunDef, fds: Set[FunDef])(implicit c: LeonContext, p: Program) {
  var numToCoverForEachExample: Int = 1
  
  /** The number of expressions is the same as the number of arguments. */
  def result(): Stream[Seq[Expr]] = {
    /* Algorithm:
     * 1) Consider only match/case and if/else statements.
     * def f(x: Int, z: Boolean): Int =
     *   x match {
     *     case 0 | 1 => 1
     *     case _ =>
     *       if(z) x*f(x-1,!z)
     *       else f(x-1,!z)+f(x-2,!z)
     *   } 
     * 2) In innermost branches, replace each result by (result, bi) where bi is a boolean described later.
     * def f(x: Int, z: Boolean): (Int, Boolean) =
     *   x match {
     *     case 0 | 1 => (1, b1)
     *     case _ =>
     *       if(z) (x*f(x-1,!z), b2)
     *       else (f(x-1,!z)+f(x-2,!z), b3)
     *   } 
     * 3) If the function is recursive, recover the previous values and left-OR them with the returning bi.
     * def f(x: Int, z: Boolean): (Int, Boolean) =
     *   x match {
     *     case 0 | 1 => (1, b1)
     *     case _ =>
     *       if(z) {
     *         val (r, bf) = f(x-1,!z)
     *         (x*r, b2 || bf)}
     *       else {
     *         val (r, bf) = f(x-1,!z)
     *         val (r2, bf2) = f(x-2,!z)
     *         (r+r2, b3 || bf || bf2)
     *       }
     *   } 
     * 4) Add the post-condition
     *   ensuring { res => !res._2 }
     * 5) Let B be the set of bi.
     *    For each b in B
     *      Set all b' in B to false except b to true
     *      Find a counter-example.
     *      yield  it in the stream.
     */
    
    /* Change all return types to accommodate the new covering boolean */
    val changeReturnTypes = { (p: Program) =>
        val (program, idMap, fdMap, cdMap) = DefOps.replaceFunDefs(p)({
          (f: FunDef) =>
            if((fds contains f) || f == fd) {
              Some(f.duplicate(returnType = TupleType(Seq(f.returnType, BooleanType))))
            } else
              None
        }, {
          (fi: FunctionInvocation, newFd: FunDef) =>
            Some(TupleSelect(FunctionInvocation(newFd.typed, fi.args), 1))
        })
        (program, fdMap(fd), fds.map(fdMap))
    }
    val addNewReturnVariables = { (p: Program, fd: FunDef, fds: Set[FunDef]) => 
      
    }
    
    (changeReturnTypes andThen
     addNewReturnVariables.tupled)(p)
    
    
    ???
  }
}