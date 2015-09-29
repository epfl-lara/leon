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
import invariant.structure.Call
import invariant.structure.FunctionUtils._
import leon.invariant.factories.TemplateIdFactory

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object ExpressionTransformer {

  val zero = InfiniteIntegerLiteral(0)
  val one = InfiniteIntegerLiteral(1)
  val mone = InfiniteIntegerLiteral(-1)
  val tru = BooleanLiteral(true)
  val fls = BooleanLiteral(false)
  val bone = BigInt(1)

  /**
   * This function conjoins the conjuncts created by 'transfomer' within the clauses containing Expr.
   * This is meant to be used by operations that may flatten subexpression using existential quantifiers.
   * @param insideFunction when set to true indicates that the newConjuncts (second argument)
   * should not conjoined to the And(..) / Or(..) expressions found because they
   * may be called inside a function.
   */
  def conjoinWithinClause(e: Expr, transformer: (Expr, Boolean) => (Expr, Set[Expr]),
    insideFunction: Boolean): (Expr, Set[Expr]) = {
      e match {
        case And(args) if !insideFunction => {
          val newargs = args.map((arg) => {
            val (nexp, ncjs) = transformer(arg, false)
            Util.createAnd(nexp +: ncjs.toSeq)
          })
          (Util.createAnd(newargs), Set())
        }

        case Or(args) if !insideFunction => {
          val newargs = args.map((arg) => {
            val (nexp, ncjs) = transformer(arg, false)
            Util.createAnd(nexp +: ncjs.toSeq)
          })
          (Util.createOr(newargs), Set())
        }

        case t: Terminal => (t, Set())

        /*case BinaryOperator(e1, e2, op) => {
          val (nexp1, ncjs1) = transformer(e1, true)
          val (nexp2, ncjs2) = transformer(e2, true)
          (op(nexp1, nexp2), ncjs1 ++ ncjs2)
        }

        case u @ UnaryOperator(e1, op) => {
          val (nexp, ncjs) = transformer(e1, true)
          (op(nexp), ncjs)
        }*/

        case n @ Operator(args, op) => {
          var ncjs = Set[Expr]()
          val newargs = args.map((arg) => {
            val (nexp, js) = transformer(arg, true)
            ncjs ++= js
            nexp
          })
          (op(newargs), ncjs)
        }
        case _ => throw new IllegalStateException("Impossible event: expr did not match any case: " + e)
      }
    }

  /**
   * Assumed that that given expression has boolean type
   * converting if-then-else and let into a logical formula
   */
  def reduceLangBlocks(inexpr: Expr, multop: (Expr, Expr) => Expr) = {

    def transform(e: Expr, insideFunction: Boolean): (Expr, Set[Expr]) = {
      e match {
        // Handle asserts here. Return flattened body as the result
        case as @ Assert(pred, _, body) => {
          val freshvar = TVarFactory.createTemp("asrtres", e.getType).toVariable
          val newexpr = Equals(freshvar, body)
          val resset = transform(newexpr, insideFunction)
          (freshvar, resset._2 + resset._1)
        }
        //handles division by constant
        case Division(lhs, rhs @ InfiniteIntegerLiteral(v)) => {
          //this models floor and not integer division
          val quo = TVarFactory.createTemp("q", IntegerType).toVariable
          var possibs = Seq[Expr]()
          for (i <- v - 1 to 0 by -1) {
            if (i == 0) possibs :+= Equals(lhs, Times(rhs, quo))
            else possibs :+= Equals(lhs, Plus(Times(rhs, quo), InfiniteIntegerLiteral(i)))
          }
          //compute the disjunction of all possibs
          val newexpr = Or(possibs)
          //println("newexpr: "+newexpr)
          val resset = transform(newexpr, true)
          (quo, resset._2 + resset._1)
        }
        //handles division by variables
        case Division(lhs, rhs) => {
          //this models floor and not integer division
          val quo = TVarFactory.createTemp("q", IntegerType).toVariable
          val rem = TVarFactory.createTemp("r", IntegerType).toVariable
          val mult = multop(quo, rhs)
          val divsem = Equals(lhs, Plus(mult, rem))
          //TODO: here, we have to use |rhs|
          val newexpr = Util.createAnd(Seq(divsem, LessEquals(zero, rem), LessEquals(rem, Minus(rhs, one))))
          val resset = transform(newexpr, true)
          (quo, resset._2 + resset._1)
        }
        case err @ Error(_, msg) => {
          //replace this by a fresh variable of the error type
          (TVarFactory.createTemp("err", err.getType).toVariable, Set[Expr]())
        }
        case Equals(lhs, rhs) => {
          val (nexp1, ncjs1) = transform(lhs, true)
          val (nexp2, ncjs2) = transform(rhs, true)
          (Equals(nexp1, nexp2), ncjs1 ++ ncjs2)
        }
        case IfExpr(cond, thn, elze) => {
          val freshvar = TVarFactory.createTemp("ifres", e.getType).toVariable
          val newexpr = Or(And(cond, Equals(freshvar, thn)), And(Not(cond), Equals(freshvar, elze)))
          val resset = transform(newexpr, insideFunction)
          (freshvar, resset._2 + resset._1)
        }
        case Let(binder, value, body) => {
          //TODO: do we have to consider reuse of let variables ?
          val (resbody, bodycjs) = transform(body, true)
          val (resvalue, valuecjs) = transform(value, true)

          (resbody, (valuecjs + Equals(binder.toVariable, resvalue)) ++ bodycjs)
        }
        //the value is a tuple in the following case
        case LetTuple(binders, value, body) => {
          //TODO: do we have to consider reuse of let variables ?
          val (resbody, bodycjs) = transform(body, true)
          val (resvalue, valuecjs) = transform(value, true)

          //here we optimize the case where resvalue itself has tuples
          val newConjuncts = resvalue match {
            case Tuple(args) => {
              binders.zip(args).map((elem) => {
                val (bind, arg) = elem
                Equals(bind.toVariable, arg)
              })
            }
            case _ => {
              //may it is better to assign resvalue to a temporary variable (if it is not already a variable)
              val (resvalue2, cjs) = resvalue match {
                case t: Terminal => (t, Seq())
                case _ => {
                  val freshres = TVarFactory.createTemp("tres", resvalue.getType).toVariable
                  (freshres, Seq(Equals(freshres, resvalue)))
                }
              }
              var i = 0
              val cjs2 = binders.map((bind) => {
                i += 1
                Equals(bind.toVariable, TupleSelect(resvalue2, i))
              })
              (cjs ++ cjs2)
            }
          }

          (resbody, (valuecjs ++ newConjuncts) ++ bodycjs)
        }
        case _ => {
          conjoinWithinClause(e, transform, false)
        }
      }
    }
    val (nexp, ncjs) = transform(inexpr, false)
    val res = if (!ncjs.isEmpty) {
      Util.createAnd(nexp +: ncjs.toSeq)
    } else nexp
    res
  }

  /**
   * Requires: The expression has to be in NNF form and without if-then-else and let constructs
   * Assumed that that given expression has boolean type
   * (a) the function replaces every function call by a variable and creates a new equality
   * (b) it also replaces arguments that are not variables by fresh variables and creates
   * a new equality mapping the fresh variable to the argument expression
   */
  def FlattenFunction(inExpr: Expr): Expr = {

    /**
     * First return value is the new expression. The second return value is the
     * set of new conjuncts
     * @param insideFunction when set to true indicates that the newConjuncts (second argument)
     * should not conjoined to the And(..) / Or(..) expressions found because they
     * may be called inside a function.
     */
    def flattenFunc(e: Expr, insideFunction: Boolean): (Expr, Set[Expr]) = {
      e match {
        case fi @ FunctionInvocation(fd, args) => {
          //now also flatten the args. The following is slightly tricky
          val (newargs, newConjuncts) = flattenArgs(args, true)
          //create a new equality in UIFs
          val newfi = FunctionInvocation(fd, newargs)
          //create a new variable to represent the function
          val freshResVar = Variable(TVarFactory.createTemp("r", fi.getType))
          val res = (freshResVar, newConjuncts + Equals(freshResVar, newfi))
          res
        }
        case inst @ IsInstanceOf(e1, cd) => {
          //replace e by a variable
          val (newargs, newcjs) = flattenArgs(Seq(e1), true)
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newInst = IsInstanceOf(freshArg, cd)
          val freshResVar = Variable(TVarFactory.createTemp("ci", inst.getType))
          newConjuncts += Equals(freshResVar, newInst)
          (freshResVar, newConjuncts)
        }
        case cs @ CaseClassSelector(cd, e1, sel) => {
          val (newargs, newcjs) = flattenArgs(Seq(e1), true)
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newCS = CaseClassSelector(cd, freshArg, sel)
          val freshResVar = Variable(TVarFactory.createTemp("cs", cs.getType))
          newConjuncts += Equals(freshResVar, newCS)

          (freshResVar, newConjuncts)
        }
        case ts @ TupleSelect(e1, index) => {
          val (newargs, newcjs) = flattenArgs(Seq(e1), true)
          var newConjuncts = newcjs

          val freshArg = newargs(0)
          val newTS = TupleSelect(freshArg, index)
          val freshResVar = Variable(TVarFactory.createTemp("ts", ts.getType))
          newConjuncts += Equals(freshResVar, newTS)

          (freshResVar, newConjuncts)
        }
        case cc @ CaseClass(cd, args) => {

          val (newargs, newcjs) = flattenArgs(args, true)
          var newConjuncts = newcjs

          val newCC = CaseClass(cd, newargs)
          val freshResVar = Variable(TVarFactory.createTemp("cc", cc.getType))
          newConjuncts += Equals(freshResVar, newCC)

          (freshResVar, newConjuncts)
        }
        case tp @ Tuple(args) => {
          val (newargs, newcjs) = flattenArgs(args, true)
          var newConjuncts = newcjs

          val newTP = Tuple(newargs)
          val freshResVar = Variable(TVarFactory.createTemp("tp", tp.getType))
          // if(freshResVar.id.toString == "tp6"){
          //   println("Creating temporary tp6 type: "+tp.getType+" expr: "+tp)
          //   throw new IllegalStateException("")
          // }
          newConjuncts += Equals(freshResVar, newTP)

          (freshResVar, newConjuncts)
        }
        case _ => conjoinWithinClause(e, flattenFunc, insideFunction)
      }
    }

    def flattenArgs(args: Seq[Expr], insideFunction: Boolean): (Seq[Expr], Set[Expr]) = {
      var newConjuncts = Set[Expr]()
      val newargs = args.map((arg) =>
        arg match {
          case v: Variable => v
          case r: ResultVariable => r
          case _ => {
            val (nexpr, ncjs) = flattenFunc(arg, insideFunction)

            newConjuncts ++= ncjs

            nexpr match {
              case v: Variable => v
              case r: ResultVariable => r
              case _ => {
                val freshArgVar = Variable(TVarFactory.createTemp("arg", arg.getType))
                newConjuncts += Equals(freshArgVar, nexpr)
                freshArgVar
              }
            }
          }
        })
      (newargs, newConjuncts)
    }

    val (nexp, ncjs) = flattenFunc(inExpr, false)
    if (!ncjs.isEmpty) {
      Util.createAnd(nexp +: ncjs.toSeq)
    } else nexp
  }

  /**
   * The following procedure converts the formula into negated normal form by pushing all not's inside.
   * It also handles disequality constraints.
   * Assumption:
   *  (a) the formula does not have match constructs
   * Some important features.
   * (a) For a strict inequality with real variables/constants, the following produces a strict inequality
   * (b) Strict inequalities with only integer variables/constants are reduced to non-strict inequalities
   */
  def TransformNot(expr: Expr, retainNEQ: Boolean = false): Expr = { // retainIff : Boolean = false
    def nnf(inExpr: Expr): Expr = {

      if (inExpr.getType != BooleanType) inExpr
      else inExpr match {
        case Not(Not(e1)) => nnf(e1)
        case e @ Not(t: Terminal) => e
        case e @ Not(FunctionInvocation(_, _)) => e
        case Not(And(args)) => Util.createOr(args.map(arg => nnf(Not(arg))))
        case Not(Or(args)) => Util.createAnd(args.map(arg => nnf(Not(arg))))
        case Not(e @ Operator(Seq(e1, e2), op)) => {
        	//matches integer binary relation or a boolean equality
          if (e1.getType == BooleanType || e1.getType == Int32Type || e1.getType == RealType || e1.getType == IntegerType) {
            e match {
              case e: Equals => {
                if (e1.getType == BooleanType && e2.getType == BooleanType) {
                  Or(And(nnf(e1), nnf(Not(e2))), And(nnf(e2), nnf(Not(e1))))
                } else {
                  if (retainNEQ) Not(Equals(e1, e2))
                  else Or(nnf(LessThan(e1, e2)), nnf(GreaterThan(e1, e2)))
                }
              }
              case e: LessThan => GreaterEquals(nnf(e1), nnf(e2))
              case e: LessEquals => GreaterThan(nnf(e1), nnf(e2))
              case e: GreaterThan => LessEquals(nnf(e1), nnf(e2))
              case e: GreaterEquals => LessThan(nnf(e1), nnf(e2))
              case e: Implies => And(nnf(e1), nnf(Not(e2)))
              case _ => throw new IllegalStateException("Unknown binary operation: " + e)
            }
          } else {
            //in this case e is a binary operation over ADTs
            e match {
              case ninst @ Not(IsInstanceOf(e1, cd)) => Not(IsInstanceOf(nnf(e1), cd))
              case e: Equals => Not(Equals(nnf(e1), nnf(e2)))
              case _ => throw new IllegalStateException("Unknown operation on algebraic data types: " + e)
            }
          }
        }
        case Implies(lhs, rhs) => nnf(Or(Not(lhs), rhs))
        case e @ Equals(lhs, IsInstanceOf(_, _) | CaseClassSelector(_, _, _) | TupleSelect(_, _) | FunctionInvocation(_, _)) =>
          //all case where rhs could use an ADT tree e.g. instanceOF, tupleSelect, fieldSelect, function invocation
          e
        case Equals(lhs, rhs) if (lhs.getType == BooleanType && rhs.getType == BooleanType) => {
          nnf(And(Implies(lhs, rhs), Implies(rhs, lhs)))
        }
        case Not(IfExpr(cond, thn, elze)) => IfExpr(nnf(cond), nnf(Not(thn)), nnf(Not(elze)))
        case Not(Let(i, v, e)) => Let(i, nnf(v), nnf(Not(e)))
        //note that Not(LetTuple) is not possible
        case t: Terminal => t
        /*case u @ UnaryOperator(e1, op) => op(nnf(e1))
        case b @ BinaryOperator(e1, e2, op) => op(nnf(e1), nnf(e2))*/
        case n @ Operator(args, op) => op(args.map(nnf(_)))

        case _ => throw new IllegalStateException("Impossible event: expr did not match any case: " + inExpr)
      }
    }
    val nnfvc = nnf(expr)
    nnfvc
  }

  /**
   * Eliminates redundant nesting of ORs and ANDs.
   * This is supposed to be a semantic preserving transformation
   */
  def pullAndOrs(expr: Expr): Expr = {

    simplePostTransform((e: Expr) => e match {
      case Or(args) => {
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case Or(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        Util.createOr(newArgs)
      }
      case And(args) => {
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case And(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        Util.createAnd(newArgs)
      }
      case _ => e
    })(expr)
  }

  def classSelToCons(e: Expr): Expr = {
    val (r, cd, ccvar, ccfld) = e match {
      case Equals(r0 @ Variable(_), CaseClassSelector(cd0, ccvar0, ccfld0)) => (r0, cd0, ccvar0, ccfld0)
      case _ => throw new IllegalStateException("Not a case-class-selector call")
    }
    //convert this to a cons by creating dummy variables
    val args = cd.fields.map((fld) => {
      if (fld.id == ccfld) r
      else {
        //create a dummy identifier there
        TVarFactory.createDummy(fld.getType).toVariable
      }
    })
    Equals(ccvar, CaseClass(cd, args))
  }

  def tupleSelToCons(e: Expr): Expr = {
    val (r, tpvar, index) = e match {
      case Equals(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
      // case Iff(r0 @ Variable(_), TupleSelect(tpvar0, index0)) => (r0, tpvar0, index0)
      case _ => throw new IllegalStateException("Not a tuple-selector call")
    }
    //convert this to a Tuple by creating dummy variables
    val tupleType = tpvar.getType.asInstanceOf[TupleType]
    val args = (1 until tupleType.dimension + 1).map((i) => {
      if (i == index) r
      else {
        //create a dummy identifier there (note that here we have to use i-1)
        TVarFactory.createDummy(tupleType.bases(i - 1)).toVariable
      }
    })
    Equals(tpvar, Tuple(args))
  }

  /**
   * Normalizes the expressions
   */
  def normalizeExpr(expr: Expr, multOp: (Expr, Expr) => Expr): Expr = {
    //reduce the language before applying flatten function
    // println("Normalizing " + ScalaPrinter(expr) + "\n")
    val redex = reduceLangBlocks(expr, multOp)
    // println("Redex: "+ScalaPrinter(redex) + "\n")
    val nnfExpr = TransformNot(redex)
    // println("NNFexpr: "+ScalaPrinter(nnfExpr) + "\n")
    //flatten all function calls
    val flatExpr = FlattenFunction(nnfExpr)
    // println("Flatexpr: "+ScalaPrinter(flatExpr) + "\n")
    //perform additional simplification
    val simpExpr = pullAndOrs(TransformNot(flatExpr))
    simpExpr
  }

  /**
   * This is the inverse operation of flattening, this is mostly
   * used to produce a readable formula.
   * Freevars is a set of identifiers that are program variables
   * This assumes that temporary identifiers (which are not freevars) are not reused across clauses.
   */
  def unFlatten(ine: Expr, freevars: Set[Identifier]): Expr = {
    var tempMap = Map[Expr, Expr]()
    val newinst = simplePostTransform((e: Expr) => e match {
      case Equals(v @ Variable(id), rhs @ _) if !freevars.contains(id) =>
        if (tempMap.contains(v)) e
        else {
          tempMap += (v -> rhs)
          tru
        }
      case _ => e
    })(ine)
    val closure = (e: Expr) => replace(tempMap, e)
    Util.fix(closure)(newinst)
  }

  /**
   * convert all integer constants to real constants
   */
  def IntLiteralToReal(inexpr: Expr): Expr = {
    val transformer = (e: Expr) => e match {
      case InfiniteIntegerLiteral(v) => FractionalLiteral(v, 1)
      case IntLiteral(v) => FractionalLiteral(v, 1)
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }

  /**
   * convert all real constants to integers
   */
  def FractionalLiteralToInt(inexpr: Expr): Expr = {
    val transformer = (e: Expr) => e match {
      case FractionalLiteral(v, `bone`) => InfiniteIntegerLiteral(v)
      case FractionalLiteral(_, _) => throw new IllegalStateException("cannot convert real literal to integer: " + e)
      case _ => e
    }
    simplePostTransform(transformer)(inexpr)
  }

  /**
   * A hacky way to implement subexpression check.
   * TODO: fix this
   */
  def isSubExpr(key: Expr, expr: Expr): Boolean = {

    var found = false
    simplePostTransform((e: Expr) => e match {
      case _ if (e == key) =>
        found = true; e
      case _ => e
    })(expr)
    found
  }

  /**
   * Some simplification rules (keep adding more and more rules)
   */
  def simplify(expr: Expr): Expr = {

    //Note: some simplification are already performed by the class constructors (see Tree.scala)
    simplePostTransform((e: Expr) => e match {
      case Equals(lhs, rhs) if (lhs == rhs) => tru
      case LessEquals(lhs, rhs) if (lhs == rhs) => tru
      case GreaterEquals(lhs, rhs) if (lhs == rhs) => tru
      case LessThan(lhs, rhs) if (lhs == rhs) => fls
      case GreaterThan(lhs, rhs) if (lhs == rhs) => fls
      case UMinus(InfiniteIntegerLiteral(v)) => InfiniteIntegerLiteral(-v)
      case Equals(InfiniteIntegerLiteral(v1), InfiniteIntegerLiteral(v2)) => BooleanLiteral(v1 == v2)
      case LessEquals(InfiniteIntegerLiteral(v1), InfiniteIntegerLiteral(v2)) => BooleanLiteral(v1 <= v2)
      case LessThan(InfiniteIntegerLiteral(v1), InfiniteIntegerLiteral(v2)) => BooleanLiteral(v1 < v2)
      case GreaterEquals(InfiniteIntegerLiteral(v1), InfiniteIntegerLiteral(v2)) => BooleanLiteral(v1 >= v2)
      case GreaterThan(InfiniteIntegerLiteral(v1), InfiniteIntegerLiteral(v2)) => BooleanLiteral(v1 > v2)
      case _ => e
    })(expr)
  }

  /**
   * Input expression is assumed to be in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed
   */
  def isDisjunct(e: Expr): Boolean = e match {
    case And(args) => args.foldLeft(true)((acc, arg) => acc && isDisjunct(arg))
    case Not(Equals(_, _)) | Not(Variable(_)) => true
    case Or(_) | Implies(_, _) | Not(_) | Equals(_, _) => false
    case _ => true
  }

  /**
   * assuming that the expression is in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed
   */
  def isConjunct(e: Expr): Boolean = e match {
    case Or(args) => args.foldLeft(true)((acc, arg) => acc && isConjunct(arg))
    case Not(Equals(_, _)) | Not(Variable(_)) => true
    case And(_) | Implies(_, _) | Not(_) | Equals(_, _) => false
    case _ => true
  }

  def PrintWithIndentation(wr: PrintWriter, expr: Expr): Unit = {

    def uniOP(e: Expr, seen: Int): Boolean = e match {
      case And(args) => {
        //have we seen an or ?
        if (seen == 2) false
        else args.foldLeft(true)((acc, arg) => acc && uniOP(arg, 1))
      }
      case Or(args) => {
        //have we seen an And ?
        if (seen == 1) false
        else args.foldLeft(true)((acc, arg) => acc && uniOP(arg, 2))
      }
      case t: Terminal => true
      /*case u @ UnaryOperator(e1, op) => uniOP(e1, seen)
      case b @ BinaryOperator(e1, e2, op) => uniOP(e1, seen) && uniOP(e2, seen)*/
      case n @ Operator(args, op) => args.foldLeft(true)((acc, arg) => acc && uniOP(arg, seen))
    }

    def printRec(e: Expr, indent: Int): Unit = {
      if (uniOP(e, 0)) wr.println(ScalaPrinter(e))
      else {
        wr.write("\n" + " " * indent + "(\n")
        e match {
          case And(args) => {
            var start = true
            args.map((arg) => {
              wr.print(" " * (indent + 1))
              if (!start) wr.print("^")
              printRec(arg, indent + 1)
              start = false
            })
          }
          case Or(args) => {
            var start = true
            args.map((arg) => {
              wr.print(" " * (indent + 1))
              if (!start) wr.print("v")
              printRec(arg, indent + 1)
              start = false
            })
          }
          case _ => throw new IllegalStateException("how can this happen ? " + e)
        }
        wr.write(" " * indent + ")\n")
      }
    }
    printRec(expr, 0)
  }

  /**
   * Converts to sum of products form by distributing
   * multiplication over addition
   */
  def normalizeMultiplication(e: Expr, multop: (Expr, Expr) => Expr): Expr = {

    def isConstantOrTemplateVar(e: Expr) = {
      e match {
        case l: Literal[_] => true
        case Variable(id) if TemplateIdFactory.IsTemplateIdentifier(id) => true
        case _ => false
      }
    }

    def distribute(e: Expr): Expr = {
      simplePreTransform(_ match {
        case e @ FunctionInvocation(TypedFunDef(fd, _), Seq(e1, e2)) if Util.isMultFunctions(fd) =>
          val newe = (e1, e2) match {
            case (Plus(sum1, sum2), _) =>
              // distribute e2 over e1
              Plus(multop(sum1, e2), multop(sum2, e2))
            case (_, Plus(sum1, sum2)) =>
              // distribute e1 over e2
              Plus(multop(e1, sum1), multop(e1, sum2))
            case (Times(arg1, arg2), _) =>
              // pull the constants out of multiplication (note: times is used when one of the arguments is a literal or template id
              if (isConstantOrTemplateVar(arg1)) {
                Times(arg1, multop(arg2, e2))
              } else
                Times(arg2, multop(arg1, e2)) // here using commutativity axiom
            case (_, Times(arg1, arg2)) =>
              if (isConstantOrTemplateVar(arg1))
                Times(arg1, multop(e1, arg2))
              else
                Times(arg2, multop(e1, arg1))
            case _ if isConstantOrTemplateVar(e1) || isConstantOrTemplateVar(e2) =>
              // here one of the operands is a literal or template var, so convert mult to times and continue
              Times(e1, e2)
            case _ =>
              e
          }
          newe
        case other => other
      })(e)
    }
    distribute(e)
  }
}
