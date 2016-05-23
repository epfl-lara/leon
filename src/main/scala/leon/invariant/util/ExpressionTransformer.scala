/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import java.io._
import purescala.ScalaPrinter
import leon.invariant.factories.TemplateIdFactory
import PredicateUtil._
import Util._
import TVarFactory._

/**
 * A collection of transformation on expressions and some utility methods.
 * These operations are mostly semantic preserving (specific assumptions/requirements are specified on the operations)
 */
object ExpressionTransformer {

  // identifier for temporaries that are generated during flattening of terms other than functions
  val flatContext = newContext
  // temporaries used in the function flattening
  val funFlatContext = newContext
  // conversion of other language constructs
  val langContext = newContext

  def createFlatTemp(name: String, tpe: TypeTree = Untyped) = createTemp(name, tpe, flatContext)

  /**
   * This function conjoins the conjuncts created by 'transfomer' within the clauses containing Expr.
   * This is meant to be used by operations that may flatten subexpression using existential quantifiers.
   * @param insideFunction when set to true indicates that the newConjuncts (second argument)
   * should not conjoined to the And(..) / Or(..) expressions found because they
   * may be called inside a function.
   * TODO: remove this function altogether and treat 'and' and 'or's as functions.
   */
  def conjoinWithinClause(e: Expr, transformer: (Expr, Boolean) => (Expr, Set[Expr]),
    insideFunction: Boolean): (Expr, Set[Expr]) = {
    e match {
      case And(args) if !insideFunction =>
        val newargs = args.map{arg =>
          val (nexp, ncjs) = transformer(arg, false)
          createAnd(nexp +: ncjs.toSeq)
        }
        (createAnd(newargs), Set())

      case Or(args) if !insideFunction =>
        val newargs = args.map{arg =>
          val (nexp, ncjs) = transformer(arg, false)
          createAnd(nexp +: ncjs.toSeq)
        }
        (createOr(newargs), Set())

      case t: Terminal => (t, Set())

      case n @ Operator(args, op) =>
        var ncjs = Set[Expr]()
        val newargs = args.map((arg) => {
          val (nexp, js) = transformer(arg, true)
          ncjs ++= js
          nexp
        })
        (op(newargs), ncjs)
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
        case as @ Assert(pred, _, body) =>
          val freshvar = createFlatTemp("asrtres", e.getType).toVariable
          val newexpr = Equals(freshvar, body)
          val resset = transform(newexpr, insideFunction)
          (freshvar, resset._2 + resset._1)

        //handles division by constant
        case Division(lhs, rhs @ InfiniteIntegerLiteral(v)) =>
          //this models floor and not integer division
          val quo = createTemp("q", IntegerType, langContext).toVariable
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

        //handles division by variables
        case Division(lhs, rhs) =>
          //this models floor and not integer division
          val quo = createTemp("q", IntegerType, langContext).toVariable
          val rem = createTemp("r", IntegerType, langContext).toVariable
          val mult = multop(quo, rhs)
          val divsem = Equals(lhs, Plus(mult, rem))
          //TODO: here, we have to use |rhs|
          val newexpr = createAnd(Seq(divsem, LessEquals(zero, rem), LessEquals(rem, Minus(rhs, one))))
          val resset = transform(newexpr, true)
          (quo, resset._2 + resset._1)

        case err @ Error(_, msg) =>
          //replace this by a fresh variable of the error type
          (createTemp("err", err.getType, langContext).toVariable, Set[Expr]())

        case Equals(lhs, rhs) =>
          val (nexp1, ncjs1) = transform(lhs, true)
          val (nexp2, ncjs2) = transform(rhs, true)
          (Equals(nexp1, nexp2), ncjs1 ++ ncjs2)

        case IfExpr(cond, thn, elze) if insideFunction =>
          val freshvar = createTemp("ifres", e.getType, langContext).toVariable
          val (ncond, condConjs) = transform(cond, true)
          val (nthen, thenConjs) = transform(Equals(freshvar, thn), false)
          val (nelze, elzeConjs) = transform(Equals(freshvar, elze), false)
          val conjs = condConjs + IfExpr(cond,
              createAnd(nthen +: thenConjs.toSeq), createAnd(nelze +: elzeConjs.toSeq))
          (freshvar, conjs)

        case IfExpr(cond, thn, elze) => // here, we are at the top, and hence can avoid creating freshids
          val (ncond, condConjs) = transform(cond, true)
          val (nthen, thenConjs) = transform(thn, false)
          val (nelze, elzeConjs) = transform(elze, false)
          (IfExpr(cond,
              createAnd(nthen +: thenConjs.toSeq), createAnd(nelze +: elzeConjs.toSeq)), condConjs)

        case Let(binder, value, body) =>
          //TODO: do we have to consider reuse of let variables ?
          val (resbody, bodycjs) = transform(body, true)
          val (resvalue, valuecjs) = transform(value, true)
          (resbody, (valuecjs + Equals(binder.toVariable, resvalue)) ++ bodycjs)

        case _ => conjoinWithinClause(e, transform, insideFunction)
      }
    }
    val (nexp, ncjs) = transform(inexpr, false)
    val res = if (ncjs.nonEmpty) {
      createAnd(nexp +: ncjs.toSeq)
    } else nexp
    res
  }

  def isAtom(e: Expr): Boolean = e match {
    case _: And | _: Or  | _: IfExpr => false
    case _ => true
  }

  def isADTTheory(e: Expr) = e match {
    case _: CaseClassSelector | _: CaseClass | _: TupleSelect | _: Tuple | _: IsInstanceOf => true
    case _ => false
  }

  def isSetTheory(e: Expr) = e match {
    case _: SetUnion | _: ElementOfSet | _: SubsetOf | _: FiniteSet => true
    case _ => false
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
        case fi @ FunctionInvocation(fd, args) =>
          val (newargs, newConjuncts) = flattenArgs(args, true)
          val freshResVar = Variable(createTemp("r", fi.getType, funFlatContext))
          (freshResVar, newConjuncts + Equals(freshResVar, FunctionInvocation(fd, newargs)))

        case adte if isADTTheory(adte) =>
          val Operator(args, op) = adte
          val freshName = adte match {
            case _: IsInstanceOf => "ci"
            case _: CaseClassSelector => "cs"
            case _: CaseClass => "cc"
            case _: TupleSelect => "ts"
            case _: Tuple => "tp"
          }
          val freshVar = Variable(createFlatTemp(freshName, adte.getType))
          val (newargs, newcjs) = flattenArgs(args, true)
          (freshVar, newcjs + Equals(freshVar, op(newargs)))

        case SetUnion(_, _) | ElementOfSet(_, _) | SubsetOf(_, _) =>
          val Operator(args, op) = e
          val (Seq(a1, a2), newcjs) = flattenArgs(args, true)
          val newexpr = op(Seq(a1, a2))
          val freshResVar = Variable(createFlatTemp("set", e.getType))
          (freshResVar, newcjs + Equals(freshResVar, newexpr))

        case fs @ FiniteSet(es, typ) =>
          val args = es.toSeq
          val (nargs, newcjs) = flattenArgs(args, true)
          val newexpr = FiniteSet(nargs.toSet, typ)
          val freshResVar = Variable(createFlatTemp("fset", fs.getType))
          (freshResVar, newcjs + Equals(freshResVar, newexpr))

        case And(args) if insideFunction =>
          val (nargs, cjs) = flattenArithmeticCtrs(args)
          (And(nargs), cjs)

        case Or(args) if insideFunction =>
          val (nargs, cjs) = flattenArithmeticCtrs(args)
          (Or(nargs), cjs)

        case IfExpr(cond, thn, elze) => // make condition of if-then-elze an atom
          val (nthen, thenConjs) = flattenFunc(thn, false)
          val (nelze, elzeConjs) = flattenFunc(elze, false)
          val (ncond, condConjs) = flattenFunc(cond, true) match {
            case r@(nc, _) if isAtom(nc) && getTemplateIds(nc).isEmpty => r
            case (nc, conjs) =>
              val condvar = createFlatTemp("cond", cond.getType).toVariable
              (condvar, conjs + Equals(condvar, nc))
          }
          (IfExpr(ncond, createAnd(nthen +: thenConjs.toSeq),
              createAnd(nelze +: elzeConjs.toSeq)), condConjs)

        case _ => conjoinWithinClause(e, flattenFunc, insideFunction)
      }
    }

    def flattenArgs(args: Seq[Expr], insideFunction: Boolean): (Seq[Expr], Set[Expr]) = {
      var newConjuncts = Set[Expr]()
      val newargs = args.map {
        case v: Variable => v
        case r: ResultVariable => r
        case arg =>
          val (nexpr, ncjs) = flattenFunc(arg, insideFunction)
          newConjuncts ++= ncjs
          nexpr match {
            case v: Variable => v
            case r: ResultVariable => r
            case _ =>
              val freshArgVar = Variable(createFlatTemp("arg", arg.getType))
              newConjuncts += Equals(freshArgVar, nexpr)
              freshArgVar
          }
      }
      (newargs, newConjuncts)
    }

    def flattenArithmeticCtrs(args: Seq[Expr]) = {
      val (flatArgs, cjs) = flattenArgs(args, true)
      var ncjs = Set[Expr]()
      val nargs = flatArgs.map {
        case farg if isArithmeticRelation(farg) != Some(false) =>
          // 'farg' is a possibly arithmetic relation.
          val argvar = createFlatTemp("ar", farg.getType).toVariable
          ncjs += Equals(argvar, farg)
          argvar
        case farg => farg
      }
      (nargs, cjs ++ ncjs)
    }

    val (nexp, ncjs) = flattenFunc(inExpr, false)
    if (ncjs.nonEmpty) {
      createAnd(nexp +: ncjs.toSeq)
    } else nexp
  }

  /**
   * note: we consider even type parameters as ADT type
   */
  def adtType(e: Expr) = {
    val tpe = e.getType
    tpe.isInstanceOf[ClassType] || tpe.isInstanceOf[TupleType] || tpe.isInstanceOf[TypeParameter]
  }

  /**
   * The following procedure converts the formula into negated normal form by pushing all not's inside.
   * It will not convert boolean equalities or inequalities to disjunctions for performance.
   * Assumption:
   *  (a) the formula does not have match constructs
   *  (b) all lets have been pulled to the top
   * Some important features.
   * (a) For a strict inequality with real variables/constants, the following produces a strict inequality
   * (b) Strict inequalities with only integer variables/constants are reduced to non-strict inequalities
   */
  def toNNF(inExpr: Expr, retainNEQ: Boolean = false): Expr = {
    def nnf(expr: Expr): Expr = {
//      /println("Invoking nnf on: "+expr)
      expr match {
        //case e if e.getType != BooleanType      => e
        case Not(Not(e1))                       => nnf(e1)
        case e @ Not(t: Terminal)               => e
        case Not(FunctionInvocation(tfd, args)) => Not(FunctionInvocation(tfd, args map nnf))
        case Not(And(args))                     => createOr(args.map(arg => nnf(Not(arg))))
        case Not(Or(args))                      => createAnd(args.map(arg => nnf(Not(arg))))
        case Not(Let(i, v, e))                  => Let(i, nnf(v), nnf(Not(e)))
        case Not(IfExpr(cond, thn, elze))       => IfExpr(nnf(cond), nnf(Not(thn)), nnf(Not(elze)))
        case Not(e @ Operator(Seq(e1, e2), op)) => // Not of binary operator ?
          e match {
            case _: LessThan => GreaterEquals(e1, e2)
            case _: LessEquals => GreaterThan(e1, e2)
            case _: GreaterThan => LessEquals(e1, e2)
            case _: GreaterEquals => LessThan(e1, e2)
            case _: Implies => And(nnf(e1), nnf(Not(e2)))
            case _: SubsetOf | _: ElementOfSet | _: SetUnion | _: FiniteSet => Not(e) // set ops
            // handle equalities (which is shared by theories)
            case _: Equals if e1.getType == BooleanType => Not(Equals(nnf(e1), nnf(e2)))
            case _: Equals if adtType(e1) || e1.getType.isInstanceOf[SetType] => Not(e) // adt or set equality
            case _: Equals if TypeUtil.isNumericType(e1.getType) =>
              if (retainNEQ) Not(Equals(e1, e2))
              else Or(nnf(LessThan(e1, e2)), nnf(GreaterThan(e1, e2)))
            case _ => throw new IllegalStateException(s"Unknown binary operation: $e arg types: ${e1.getType},${e2.getType}")
          }
        case Implies(lhs, rhs) => nnf(Or(Not(lhs), rhs))
        case Equals(lhs, rhs @ (_: SubsetOf | _: ElementOfSet | _: IsInstanceOf | _: TupleSelect | _: CaseClassSelector)) =>
          Equals(nnf(lhs), rhs)
        case Equals(lhs, FunctionInvocation(tfd, args)) =>
          Equals(nnf(lhs), FunctionInvocation(tfd, args map nnf))
        case Equals(lhs, rhs) if lhs.getType == BooleanType => Equals(nnf(lhs), nnf(rhs))
        case t: Terminal => t
        case n @ Operator(args, op) => op(args map nnf)
        case _ => throw new IllegalStateException("Impossible event: expr did not match any case: " + inExpr)
      }
    }
    nnf(inExpr)
  }

  /**
   * Eliminates redundant nesting of ORs and ANDs.
   * This is supposed to be a semantic preserving transformation
   */
  def pullAndOrs(expr: Expr): Expr = {
    simplePostTransform {
      case Or(args) =>
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case Or(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        createOr(newArgs)
      case And(args) =>
        val newArgs = args.foldLeft(Seq[Expr]())((acc, arg) => arg match {
          case And(inArgs) => acc ++ inArgs
          case _ => acc :+ arg
        })
        createAnd(newArgs)
      case e => e
    }(expr)
  }

  /**
   * Normalizes the expressions
   */
  def normalizeExpr(expr: Expr, multOp: (Expr, Expr) => Expr): Expr = {
    //println("Normalizing " + ScalaPrinter(expr) + "\n")
    val redex = reduceLangBlocks(toNNF(matchToIfThenElse(expr)), multOp)
    //println("After reducing lang blocks: " + ScalaPrinter(redex) + "\n")
    val flatExpr = FlattenFunction(redex)
    val simpExpr = pullAndOrs(flatExpr)
    //println("After Normalizing: " + ScalaPrinter(flatExpr) + "\n")
    simpExpr
  }

  /**
   * This is the inverse operation of flattening.
   * This is used to produce a readable formula or more efficiently
   * solvable formulas.
   * Note: this is a helper method that assumes that 'flatIds'
   * are not shared across disjuncts.
   * If this is not guaranteed to hold, use the 'unflatten' method
   */
  def simpleUnflattenWithMap(ine: Expr, excludeIds: Set[Identifier] = Set(),
      includeFuns: Boolean): (Expr, Map[Identifier,Expr]) = {

    def isFlatTemp(id: Identifier) =
      isTemp(id, flatContext) || (includeFuns && isTemp(id, funFlatContext))

    var idMap = Map[Identifier, Expr]()
    /**
     * Here, relying on library transforms is dangerous as they
     * can perform additional simplifications to the expression on-the-fly,
     * which is not desirable here.
     */
    def rec(e: Expr): Expr = e match {
      case e @ Equals(Variable(id), rhs @ _) if isFlatTemp(id) && !excludeIds(id) =>
        val nrhs = rec(rhs)
        if (idMap.contains(id)) Equals(Variable(id), nrhs)
        else {
          idMap += (id -> nrhs)
          tru
        }
      // specially handle boolean function to prevent unnecessary simplifications
      case Or(args)           => Or(args map rec)
      case And(args)          => And(args map rec)
      case IfExpr(cond, th, elze) => IfExpr(rec(cond), rec(th), rec(elze))
      case e => e // we should not recurse in other operations, note: Not(equals) should not be considered
    }
    val newe = rec(ine)
    val closure = (e: Expr) => replaceFromIDs(idMap, e)
    val rese = fix(closure)(newe)
    (rese, idMap)
  }

  def unflattenWithMap(ine: Expr, excludeIds: Set[Identifier] = Set(),
      includeFuns: Boolean = true): (Expr, Map[Identifier,Expr]) = {
    simpleUnflattenWithMap(ine, sharedIds(ine) ++ excludeIds, includeFuns)
  }

  def unflatten(ine: Expr) = unflattenWithMap(ine)._1

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
    simplePostTransform {
      case e if (e == key) =>
        found = true; e
      case e => e
    }(expr)
    found
  }

  /**
   * Some simplification rules (keep adding more and more rules)
   */
  def simplify(expr: Expr): Expr = {
    //Note: some simplification are already performed by the class constructors (see Tree.scala)
    simplePostTransform {
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
      case e => e
    }(expr)
  }

  /**
   * Input expression is assumed to be in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed
   */
  def isDisjunct(e: Expr): Boolean = e match {
    case And(args) => args.forall(arg => isDisjunct(arg))
    case Not(Equals(_, _)) | Not(Variable(_)) => true
    case Or(_) | Implies(_, _) | Not(_) | Equals(_, _) => false
    case _ => true
  }

  /**
   * assuming that the expression is in nnf form
   * Note: (a) Not(Equals()) and Not(Variable) is allowed
   */
  def isConjunct(e: Expr): Boolean = e match {
    case Or(args) => args.forall(arg => isConjunct(arg))
    case Not(Equals(_, _)) | Not(Variable(_)) => true
    case And(_) | Implies(_, _) | Not(_) | Equals(_, _) => false
    case _ => true
  }

  def PrintWithIndentation(filePrefix: String, expr: Expr): Unit = {

    val filename = filePrefix + FileCountGUID.getID + ".txt"
    val wr = new PrintWriter(new File(filename))

    def uniOP(e: Expr, seen: Int): Boolean = e match {
      case And(args) => {
        //have we seen an or ?
        if (seen == 2) false
        else args.forall(arg => uniOP(arg, 1))
      }
      case Or(args) => {
        //have we seen an And ?
        if (seen == 1) false
        else args.forall(arg => uniOP(arg, 2))
      }
      case t: Terminal => true
      case n @ Operator(args, op) => args.forall(arg => uniOP(arg, seen))
    }

    def printRec(e: Expr, indent: Int): Unit = {
      if (uniOP(e, 0)) wr.println(ScalaPrinter(e))
      else {
        wr.write("\n" + " " * indent + "(\n")
        e match {
          case And(args) => {
            var start = true
            args.foreach((arg) => {
              wr.print(" " * (indent + 1))
              if (!start) wr.print("^")
              printRec(arg, indent + 1)
              start = false
            })
          }
          case Or(args) => {
            var start = true
            args.foreach((arg) => {
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
    wr.close()
    println("Printed to file: " + filename)
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
      simplePreTransform {
        case e @ FunctionInvocation(TypedFunDef(fd, _), Seq(e1, e2)) if isMultFunctions(fd) =>
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
      }(e)
    }
    distribute(e)
  }
}
