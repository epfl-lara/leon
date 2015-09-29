package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import java.io._
import purescala.ScalaPrinter
import leon.utils._

import invariant.structure.Call
import invariant.structure.FunctionUtils._
import leon.transformations.InstUtil._

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object LetTupleSimplification {

  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)
  val bone = BigInt(1)

  def letSanityChecks(ine: Expr) = {
    simplePostTransform(_ match {
      case letExpr @ Let(binderId, letValue, body)
      	if (binderId.getType != letValue.getType) =>
          throw new IllegalStateException("Binder and value type mismatch: "+
              s"(${binderId.getType},${letValue.getType})")
      case e => e
    })(ine)
  }

  /**
   * This function simplifies lets of the form <Var> = <TupleType Expr> by replacing
   * uses of the <Var>._i by the approppriate expression in the let body or by
   * introducing a new let <Var'> = <Var>._i and using <Var'> in place of <Var>._i
   * in the original let body.
   * Caution: this function may not be idempotent.
   */
  def simplifyTuples(ine: Expr): Expr = {

    var processedLetBinders = Set[Identifier]()
    def recSimplify(e: Expr, replaceMap: Map[Expr, Expr]): Expr = {

      //println("Before: "+e)
      val transe = e match {
        case letExpr @ Let(binderId, letValue, body) if !processedLetBinders(binderId) =>
          processedLetBinders += binderId
          // transform the 'letValue' with the current map
          val nvalue = recSimplify(letValue, replaceMap)
          // enrich the map if letValue is of tuple type
          nvalue.getType match {
            case TupleType(argTypes) =>
              var freshBinders = Set[Identifier]()
              def freshBinder(typ: TypeTree) = {
                val freshid = TVarFactory.createTemp(binderId.name, typ)
                freshBinders += freshid
                freshid.toVariable
              }
              val newmap: Map[Expr, Expr] = nvalue match {
                case Tuple(args) => // this is an optimization for the case where nvalue is a tuple
                  args.zipWithIndex.map {
                    case (t: Terminal, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> t)
                    case (_, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> freshBinder(argTypes(index)))
                  }.toMap
                case _ =>
                  argTypes.zipWithIndex.map {
                    case (argtype, index) =>
                      (TupleSelect(binderId.toVariable, index + 1) -> freshBinder(argtype))
                  }.toMap
              }
              // transform the body using the new map + old map
              val nbody = recSimplify(body, replaceMap ++ newmap)
              val bodyFreevars = variablesOf(nbody)
              // create a sequence of lets for the freshBinders
              val nletBody = newmap.foldLeft(nbody) {
                case (acc, (k, Variable(id))) if freshBinders(id) && bodyFreevars(id) =>
                  // here, the 'id' is a newly created binder and is also used in the transformed body
                  Let(id, k, acc)
                case (acc, _) =>
                  acc
              }
              Let(binderId, nvalue, nletBody)
            case _ =>
              // no simplification can be done in this step
              Let(binderId, nvalue, recSimplify(body, replaceMap))
          }
        case ts @ TupleSelect(_, _) if replaceMap.contains(ts) =>
          postMap(replaceMap.lift, true)(e) //perform recursive replacements to handle nested tuple selects
        //replaceMap(ts) //replace tuple-selects in the map with the new identifier

        case t: Terminal => t

        /*case UnaryOperator(sube, op) =>
          op(recSimplify(sube, replaceMap))

        case BinaryOperator(e1, e2, op) =>
          op(recSimplify(e1, replaceMap), recSimplify(e2, replaceMap))*/

        case Operator(subes, op) =>
          op(subes.map(recSimplify(_, replaceMap)))
      }
      //println("After: "+e)
      transe
    }
    fixpoint((e: Expr) => simplifyArithmetic(recSimplify(e, Map())))(ine)
  }

  // sanity checks
  def checkTupleSelectInsideMax(e: Expr): Boolean = {
    //exists( predicate: Expr => Expr) (e)
    var error = false
    def helper(e: Expr): Unit = {
      e match {
        case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {

          val Seq(arg1: Expr, arg2: Expr) = args
          (arg1, arg2) match {
            case (_: TupleSelect, _) => error = true
            case (_, _: TupleSelect) => error = true
            case _ => { ; }
          }
        }

        case _ => { ; }
      }
    }

    postTraversal(helper)(e)
    error
  }

  def simplifyMax(ine: Expr): Expr = {
    val debugMaxSimplify = false
    //computes a lower bound value, assuming that every sub-term used in the term is positive
    //Note: this is applicable only to expressions involving depth
    def positiveTermLowerBound(e: Expr): Int = e match {
      case IntLiteral(v) => v
      case Plus(l, r) => positiveTermLowerBound(l) + positiveTermLowerBound(r)
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
        val Seq(arg1, arg2) = args
        val lb1 = positiveTermLowerBound(arg1)
        val lb2 = positiveTermLowerBound(arg2)
        if (lb1 >= lb2) lb1 else lb2
      }
      case _ => 0 //other case are not handled as they do not appear
    }

    //checks if 'sub' is subsumed by 'e' i.e, 'e' will always take a value
    // greater than or equal to 'sub'.
    //Assuming that every sub-term used in the term is positive
    def subsumedBy(sub: Expr, e: Expr): Boolean = e match {
      case _ if (sub == e) => true
      case Plus(l, r) => subsumedBy(sub, l) || subsumedBy(sub, r)
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) =>
        val Seq(l, r) = args
        subsumedBy(sub, l) || subsumedBy(sub, r)
      case _ => false
    }

    // in the sequel, we are using the fact that 'depth' is positive and
    // 'ine' contains only 'depth' variables
    val simpe = simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
        if (debugMaxSimplify) {
          println("Simplifying: " + e)
        }
        val newargs: Seq[Expr] = args.map(simplifyArithmetic)
        val Seq(arg1: Expr, arg2: Expr) = newargs
        val simpval = if (!Util.hasCalls(arg1) && !Util.hasCalls(arg2)) {
          import invariant.structure.LinearConstraintUtil._
          val lt = exprToTemplate(LessEquals(Minus(arg1, arg2), InfiniteIntegerLiteral(0)))
          //now, check if all the variables in 'lt' have only positive coefficients
          val allPositive = lt.coeffTemplate.forall(entry => entry match {
            case (k, IntLiteral(v)) if (v >= 0) => true
            case _ => false
          }) && (lt.constTemplate match {
            case None => true
            case Some(IntLiteral(v)) if (v >= 0) => true
            case _ => false
          })
          if (allPositive) arg1
          else {
            val allNegative = lt.coeffTemplate.forall(entry => entry match {
              case (k, IntLiteral(v)) if (v <= 0) => true
              case _ => false
            }) && (lt.constTemplate match {
              case None => true
              case Some(IntLiteral(v)) if (v <= 0) => true
              case _ => false
            })
            if (allNegative) arg2
            else FunctionInvocation(tfd, newargs) //here we cannot do any simplification.
          }

        } else {
          (arg1, arg2) match {
            case (IntLiteral(v), r) if (v <= positiveTermLowerBound(r)) => r
            case (l, IntLiteral(v)) if (v <= positiveTermLowerBound(l)) => l
            case (l, r) if subsumedBy(l, r) => r
            case (l, r) if subsumedBy(r, l) => l
            case _ => FunctionInvocation(tfd, newargs)
          }
        }
        if (debugMaxSimplify) {
          println("Simplified value: " + simpval)
        }
        simpval
      }
      // case FunctionInvocation(tfd, args) if(tfd.fd.id.name == "max") => {
      // throw new IllegalStateException("Found just max in expression " + e + "\n")
      // }
      case _ => e
    })(ine)
    simpe
  }

  def inlineMax(ine: Expr): Expr = {
    //inline 'max' operations here
    simplePostTransform((e: Expr) => e match {
      case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) =>
        val Seq(arg1, arg2) = args
        val bindWithLet = (value: Expr, body: (Expr with Terminal) => Expr) => {
          value match {
            case t: Terminal => body(t)
            case Let(id, v, b: Terminal) =>
              //here we can use 'b' in 'body'
              Let(id, v, body(b))
            case _ =>
              val mt = TVarFactory.createTemp("mt", value.getType)
              Let(mt, value, body(mt.toVariable))
          }
        }
        bindWithLet(arg1, a1 => bindWithLet(arg2, a2 =>
          IfExpr(GreaterEquals(a1, a2), a1, a2)))
      case _ => e
    })(ine)
  }

  def removeLetsFromLetValues(ine: Expr): Expr = {

    /**
     * Navigates through the sequence of lets in 'e'
     * and replaces its 'let' free part by subst.
     * Assuming that 'e' has only lets at the top and no nested lets in the value
     */
    def replaceLetBody(e: Expr, subst: Expr => Expr): Expr = e match {
      case Let(binder, letv, letb) =>
        Let(binder, letv, replaceLetBody(letb, subst))
      case _ =>
        subst(e)
    }

    // the function removes the lets from the let values
    // by pulling them out
    def pullLetToTop(e: Expr): Expr = {
      val transe = e match {
        //note: do not pull let's out of ensuring or requires
        case Ensuring(body, pred) =>
          Ensuring(pullLetToTop(body), pred)
        case Require(pre, body) =>
          Require(pre, pullLetToTop(body))

        case letExpr @ Let(binder, letValue, body) =>
          // transform the 'letValue' with the current map
          pullLetToTop(letValue) match {
            case sublet @ Let(binder2, subvalue, subbody) =>
              // transforming "let v = (let v1 = e1 in e2) in e3"
              // to "let v1 = e1 in (let v = e2 in e3)"
              // here, subvalue is free of lets, but subbody may again be a let
              val newbody = replaceLetBody(subbody, Let(binder, _, pullLetToTop(body)))
              Let(binder2, subvalue, newbody)
            case nval =>
              // here, there is no let in the value
              Let(binder, nval, pullLetToTop(body))
          }
        case t: Terminal => t
        case Operator(Seq(sube), op) =>
          replaceLetBody(pullLetToTop(sube), e => op(Seq(e)))

        case Operator(Seq(e1, e2), op) =>
          replaceLetBody(pullLetToTop(e1), te1 =>
            replaceLetBody(pullLetToTop(e2), te2 => op(Seq(te1, te2))))

        //don't pull things out of if-then-else and match (don't know why this is a problem)
        case IfExpr(c, th, elze) =>
          IfExpr(pullLetToTop(c), pullLetToTop(th), pullLetToTop(elze))

        case Operator(Seq(), op) =>
          op(Seq())

        case Operator(subes, op) =>
          // transform all the sub-expressions
          val nsubes = subes map pullLetToTop
          //collects all the lets and makes the bodies a tuple
          var i = -1
          val transLet = nsubes.tail.foldLeft(nsubes.head) {
            case (acc, nsube) =>
              i += 1
              replaceLetBody(acc, e1 =>
                replaceLetBody(nsube, e2 => e1 match {
                  case _ if i == 0 =>
                    Tuple(Seq(e1, e2))
                  case Tuple(args) =>
                    Tuple(args :+ e2)
                }))
          }
          replaceLetBody(transLet, (e: Expr) => e match {
            case Tuple(args) =>
              op(args)
            case _ => op(Seq(e)) //here, there was only one argument
          })
      }
      transe
    }
    val res = pullLetToTop(matchToIfThenElse(ine))
    // println("After Pulling lets to top : \n" + ScalaPrinter.apply(res))
    res
  }

  def simplifyLetsAndLetsWithTuples(ine: Expr) = {

    def simplerLet(t: Expr): Option[Expr] = {
      val res = t match {
        case letExpr @ Let(i, t: Terminal, b) =>
          Some(replace(Map(Variable(i) -> t), b))

        // check if the let can be completely removed
        case letExpr @ Let(i, e, b) => {
          val occurrences = count {
            case Variable(x) if x == i => 1
            case _ => 0
          }(b)

          if (occurrences == 0) {
            Some(b)
          } else if (occurrences == 1) {
            Some(replace(Map(Variable(i) -> e), b))
          } else {
        	 //TODO: we can also remove zero occurrences and compress the tuples
            // this may be necessary when instrumentations are combined.
            letExpr match {
              case letExpr @ Let(binder, lval @ Tuple(subes), b) =>
                def occurrences(index: Int) = {
                  val res = count {
                    case TupleSelect(sel, i) if sel == binder.toVariable && i == index => 1
                    case _ => 0
                  }(b)
                  res
                }
                val repmap: Map[Expr, Expr] = subes.zipWithIndex.collect {
                  case (sube, i) if occurrences(i + 1) == 1 =>
                    (TupleSelect(binder.toVariable, i + 1) -> sube)
                }.toMap
                Some(Let(binder, lval, replace(repmap, b)))
              //note: here, we cannot remove the let,
              //if it is not used it will be removed in the next iteration

              case _ => None
            }
          }
        }

        case _ => None
      }
      res
    }

    val transforms = removeLetsFromLetValues _ andThen fixpoint(postMap(simplerLet)) _ andThen simplifyArithmetic
    transforms(ine)
  }

  /*
    This function tries to simplify a part of the expression tree consisting of the same operation.
    The operatoin needs to be associative and commutative for this simplification to work .
    Arguments:
      op: An implementation of the opertaion to be simplified
      getLeaves: Gets all the operands from the AST (if the argument is not of
                  the form currently being simplified, this is required to return an empty set)
      identity: The identity element for the operation
      makeTree: Makes an AST from the operands
  */
  def simplifyConstantsGeneral(e: Expr, op: (BigInt, BigInt) => BigInt,
    getLeaves: (Expr, Boolean) => Seq[Expr], identity: BigInt,
    makeTree: (Expr, Expr) => Expr): Expr = {

    val allLeaves = getLeaves(e, true)
    // Here the expression is not of the form we are currently simplifying
    if (allLeaves.size == 0) e
    else {
      // fold constants here
      val allConstantsOpped = allLeaves.foldLeft(identity)((acc, e) => e match {
        case InfiniteIntegerLiteral(x) => op(acc, x)
        case _ => acc
      })

      val allNonConstants = allLeaves.filter((e) => e match {
        case _: InfiniteIntegerLiteral => false
        case _ => true
      })

      // Reconstruct the expressin tree with the non-constants and the result of constant evaluation above
      if (allConstantsOpped != identity) {
        allNonConstants.foldLeft(InfiniteIntegerLiteral(allConstantsOpped): Expr)((acc: Expr, currExpr) => makeTree(acc, currExpr))
      }
      else {
        if (allNonConstants.size == 0) InfiniteIntegerLiteral(identity)
        else {
          allNonConstants.tail.foldLeft(allNonConstants.head)((acc: Expr, currExpr) => makeTree(acc, currExpr))
        }
      }
    }
  }

  //Use the above function to simplify additions and maximums interleaved
  def simplifyAdditionsAndMax(e: Expr): Expr = {
    def getAllSummands(e: Expr, isTopLevel: Boolean): Seq[Expr] = {
      e match {
        case Plus(e1, e2) => {
          getAllSummands(e1, false) ++ getAllSummands(e2, false)
        }
        case _ => if (isTopLevel) Seq[Expr]()  else Seq[Expr](e)
      }
    }

    def getAllMaximands(e: Expr, isTopLevel: Boolean): Seq[Expr] = {
      e match {
        case FunctionInvocation(tfd, args) if (tfd.fd == maxFun) => {
          args.foldLeft(Seq[Expr]())((accSet, e) => accSet ++ getAllMaximands(e, false))
        }
        case _ => if (isTopLevel) Seq[Expr]() else Seq[Expr](e)
      }
    }

    simplePostTransform(e => {
      val plusSimplifiedExpr =
        simplifyConstantsGeneral(e, _ + _, getAllSummands, 0, ((e1, e2) => Plus(e1, e2)))

      // Maximum simplification assumes all arguments to max
      // are non-negative (and hence 0 is the identity)
      val maxSimplifiedExpr =
        simplifyConstantsGeneral(plusSimplifiedExpr,
          ((a: BigInt, b: BigInt) => if (a > b) a else b),
          getAllMaximands,
          0,
          ((e1, e2) => {
            val typedMaxFun = TypedFunDef(maxFun, Seq())
            FunctionInvocation(typedMaxFun, Seq(e1, e2))
          }))

      maxSimplifiedExpr
    })(e)
  }
}