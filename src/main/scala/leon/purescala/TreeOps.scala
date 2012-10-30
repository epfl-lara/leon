package leon
package purescala

import leon.solvers.Solver

object TreeOps {
  import Common._
  import TypeTrees._
  import Definitions._
  import Trees._
  import Extractors._

  def negate(expr: Expr) : Expr = expr match {
    case Let(i,b,e) => Let(i,b,negate(e))
    case Not(e) => e
    case Iff(e1,e2) => Iff(negate(e1),e2)
    case Implies(e1,e2) => And(e1, negate(e2))
    case Or(exs) => And(exs map negate)
    case And(exs) => Or(exs map negate)
    case LessThan(e1,e2) => GreaterEquals(e1,e2)
    case LessEquals(e1,e2) => GreaterThan(e1,e2)
    case GreaterThan(e1,e2) => LessEquals(e1,e2)
    case GreaterEquals(e1,e2) => LessThan(e1,e2)
    case i @ IfExpr(c,e1,e2) => IfExpr(c, negate(e1), negate(e2)).setType(i.getType)
    case BooleanLiteral(b) => BooleanLiteral(!b)
    case _ => Not(expr)
  }

  // Warning ! This may loop forever if the substitutions are not
  // well-formed!
  def replace(substs: Map[Expr,Expr], expr: Expr) : Expr = {
    searchAndReplaceDFS(substs.get)(expr)
  }

  // Can't just be overloading because of type erasure :'(
  def replaceFromIDs(substs: Map[Identifier,Expr], expr: Expr) : Expr = {
    replace(substs.map(p => (Variable(p._1) -> p._2)), expr)
  }

  def searchAndReplace(subst: Expr=>Option[Expr], recursive: Boolean=true)(expr: Expr) : Expr = {
    def rec(ex: Expr, skip: Expr = null) : Expr = (if (ex == skip) None else subst(ex)) match {
      case Some(newExpr) => {
        if(newExpr.getType == Untyped) {
          Settings.reporter.error("REPLACING IN EXPRESSION WITH AN UNTYPED TREE ! " + ex + " --to--> " + newExpr)
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
        case l @ LetVar(i,e,b) => {
          val re = rec(e)
          val rb = rec(b)
          if(re != e || rb != b)
            LetVar(i, re, rb).setType(l.getType)
          else
            l
        }
        case l @ LetDef(fd, b) => {
          //TODO, not sure, see comment for the next LetDef
          fd.body = fd.body.map(rec(_))
          fd.precondition = fd.precondition.map(rec(_))
          fd.postcondition = fd.postcondition.map(rec(_))
          LetDef(fd, rec(b)).setType(l.getType)
        }

        case lt @ LetTuple(ids, expr, body) => {
          val re = rec(expr)
          val rb = rec(body)
          if (re != expr || rb != body) {
            LetTuple(ids, re, rb).setType(lt.getType)
          } else {
            lt
          }
        }
        case n @ NAryOperator(args, recons) => {
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
            recons(rargs).setType(n.getType)
          else
            n
        }
        case b @ BinaryOperator(t1,t2,recons) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          if(r1 != t1 || r2 != t2)
            recons(r1,r2).setType(b.getType)
          else
            b
        }
        case u @ UnaryOperator(t,recons) => {
          val r = rec(t)
          if(r != t)
            recons(r).setType(u.getType)
          else
            u
        }
        case i @ IfExpr(t1,t2,t3) => {
          val r1 = rec(t1)
          val r2 = rec(t2)
          val r3 = rec(t3)
          if(r1 != t1 || r2 != t2 || r3 != t3)
            IfExpr(rec(t1),rec(t2),rec(t3)).setType(i.getType)
          else
            i
        }
        case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut), cses.map(inCase(_))).setType(m.getType).setPosInfo(m)

        case c @ Choose(args, body) =>
          val body2 = rec(body)

          if (body != body2) {
            Choose(args, body2).setType(c.getType)
          } else {
            c
          }

        case t if t.isInstanceOf[Terminal] => t
        case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplace: " + unhandled)
      }
    }

    def inCase(cse: MatchCase) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard), rec(rhs))
    }

    rec(expr)
  }

  def searchAndReplaceDFS(subst: Expr=>Option[Expr])(expr: Expr) : Expr = {
    val (res,_) = searchAndReplaceDFSandTrackChanges(subst)(expr)
    res
  }

  def searchAndReplaceDFSandTrackChanges(subst: Expr=>Option[Expr])(expr: Expr) : (Expr,Boolean) = {
    var somethingChanged: Boolean = false
    def applySubst(ex: Expr) : Expr = subst(ex) match {
      case None => ex
      case Some(newEx) => {
        somethingChanged = true
        if(newEx.getType == Untyped) {
          Settings.reporter.warning("REPLACING [" + ex + "] WITH AN UNTYPED EXPRESSION !")
          Settings.reporter.warning("Here's the new expression: " + newEx)
        }
        newEx
      }
    }

    def rec(ex: Expr) : Expr = ex match {
      case l @ Let(i,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        applySubst(if(re != e || rb != b) {
          Let(i,re,rb).setType(l.getType)
        } else {
          l
        })
      }
      case l @ LetTuple(ids,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        applySubst(if(re != e || rb != b) {
          LetTuple(ids,re,rb).setType(l.getType)
        } else {
          l
        })
      }
      case l @ LetVar(i,e,b) => {
        val re = rec(e)
        val rb = rec(b)
        applySubst(if(re != e || rb != b) {
          LetVar(i,re,rb).setType(l.getType)
        } else {
          l
        })
      }
      case l @ LetDef(fd,b) => {
        //TODO: Not sure: I actually need the replace to occurs even in the pre/post condition, hope this is correct
        fd.body = fd.body.map(rec(_))
        fd.precondition = fd.precondition.map(rec(_))
        fd.postcondition = fd.postcondition.map(rec(_))
        val rl = LetDef(fd, rec(b)).setType(l.getType)
        applySubst(rl)
      }
      case n @ NAryOperator(args, recons) => {
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
        applySubst(if(change) {
          recons(rargs).setType(n.getType)
        } else {
          n
        })
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        applySubst(if(r1 != t1 || r2 != t2) {
          recons(r1,r2).setType(b.getType)
        } else {
          b
        })
      }
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t)
        applySubst(if(r != t) {
          recons(r).setType(u.getType)
        } else {
          u
        })
      }
      case i @ IfExpr(t1,t2,t3) => {
        val r1 = rec(t1)
        val r2 = rec(t2)
        val r3 = rec(t3)
        applySubst(if(r1 != t1 || r2 != t2 || r3 != t3) {
          IfExpr(r1,r2,r3).setType(i.getType)
        } else {
          i
        })
      }
      case m @ MatchExpr(scrut,cses) => {
        val rscrut = rec(scrut)
        val (newCses,changes) = cses.map(inCase(_)).unzip
        applySubst(if(rscrut != scrut || changes.exists(res=>res)) {
          MatchExpr(rscrut, newCses).setType(m.getType).setPosInfo(m)
        } else {
          m
        })
      }

      case c @ Choose(args, body) =>
        val body2 = rec(body)

        applySubst(if (body != body2) {
          Choose(args, body2).setType(c.getType).setPosInfo(c)
        } else {
          c
        })

      case t if t.isInstanceOf[Terminal] => applySubst(t)
      case unhandled => scala.sys.error("Non-terminal case should be handled in searchAndReplaceDFS: " + unhandled)
    }

    def inCase(cse: MatchCase) : (MatchCase,Boolean) = cse match {
      case s @ SimpleCase(pat, rhs) => {
        val rrhs = rec(rhs)
        if(rrhs != rhs) {
          (SimpleCase(pat, rrhs), true)
        } else {
          (s, false)
        }
      }
      case g @ GuardedCase(pat, guard, rhs) => {
        val rguard = rec(guard)
        val rrhs = rec(rhs)
        if(rguard != guard || rrhs != rhs) {
          (GuardedCase(pat, rguard, rrhs), true)
        } else {
          (g, false)
        }
      }
    }

    val res = rec(expr)
    (res, somethingChanged)
  }

  // rewrites pattern-matching expressions to use fresh variables for the binders
  def freshenLocals(expr: Expr) : Expr = {
    def rewritePattern(p: Pattern, sm: Map[Identifier,Identifier]) : Pattern = p match {
      case InstanceOfPattern(Some(b), ctd) => InstanceOfPattern(Some(sm(b)), ctd)
      case WildcardPattern(Some(b)) => WildcardPattern(Some(sm(b)))
      case CaseClassPattern(ob, ccd, sps) => CaseClassPattern(ob.map(sm(_)), ccd, sps.map(rewritePattern(_, sm)))
      case other => other
    }

    def freshenCase(cse: MatchCase) : MatchCase = {
      val allBinders: Set[Identifier] = cse.pattern.binders
      val subMap: Map[Identifier,Identifier] = Map(allBinders.map(i => (i, FreshIdentifier(i.name, true).setType(i.getType))).toSeq : _*)
      val subVarMap: Map[Expr,Expr] = subMap.map(kv => (Variable(kv._1) -> Variable(kv._2)))
      
      cse match {
        case SimpleCase(pattern, rhs) => SimpleCase(rewritePattern(pattern, subMap), replace(subVarMap, rhs))
        case GuardedCase(pattern, guard, rhs) => GuardedCase(rewritePattern(pattern, subMap), replace(subVarMap, guard), replace(subVarMap, rhs))
      }
    }

    def applyToTree(e : Expr) : Option[Expr] = e match {
      case m @ MatchExpr(s, cses) => Some(MatchExpr(s, cses.map(freshenCase(_))).setType(m.getType).setPosInfo(m))
      case l @ Let(i,e,b) => {
        val newID = FreshIdentifier(i.name, true).setType(i.getType)
        Some(Let(newID, e, replace(Map(Variable(i) -> Variable(newID)), b)))
      }
      case _ => None
    }

    searchAndReplaceDFS(applyToTree)(expr)
  }

  // convert describes how to compute a value for the leaves (that includes
  // functions with no args.)
  // combine descriess how to combine two values
  def treeCatamorphism[A](convert: Expr=>A, combine: (A,A)=>A, expression: Expr) : A = {
    treeCatamorphism(convert, combine, (e:Expr,a:A)=>a, expression)
  }
  // compute allows the catamorphism to change the combined value depending on the tree
  def treeCatamorphism[A](convert: Expr=>A, combine: (A,A)=>A, compute: (Expr,A)=>A, expression: Expr) : A = {
    def rec(expr: Expr) : A = expr match {
      case l @ Let(_, e, b) => compute(l, combine(rec(e), rec(b)))
      case l @ LetVar(_, e, b) => compute(l, combine(rec(e), rec(b)))
      case l @ LetDef(fd, b) => {//TODO, still not sure about the semantic
        val exprs: Seq[Expr] = fd.precondition.toSeq ++ fd.body.toSeq ++ fd.postcondition.toSeq ++ Seq(b)
        compute(l, exprs.map(rec(_)).reduceLeft(combine))
      }
      case n @ NAryOperator(args, _) => {
        if(args.size == 0)
          compute(n, convert(n))
        else
          compute(n, args.map(rec(_)).reduceLeft(combine))
      }
      case b @ BinaryOperator(a1,a2,_) => compute(b, combine(rec(a1),rec(a2)))
      case u @ UnaryOperator(a,_) => compute(u, rec(a))
      case i @ IfExpr(a1,a2,a3) => compute(i, combine(combine(rec(a1), rec(a2)), rec(a3)))
      case m @ MatchExpr(scrut, cses) => compute(m, (scrut +: cses.flatMap(_.expressions)).map(rec(_)).reduceLeft(combine))
      case a @ AnonymousFunction(es, ev) => compute(a, (es.flatMap(e => e._1 ++ Seq(e._2)) ++ Seq(ev)).map(rec(_)).reduceLeft(combine))
      case c @ Choose(args, body) => compute(c, rec(body))
      case t: Terminal => compute(t, convert(t))
      case unhandled => scala.sys.error("Non-terminal case should be handled in treeCatamorphism: " + unhandled)
    }

    rec(expression)
  }

  def flattenBlocks(expr: Expr): Expr = {
    def applyToTree(expr: Expr): Option[Expr] = expr match {
      case Block(exprs, last) => {
        val nexprs = (exprs :+ last).flatMap{
          case Block(es2, el) => es2 :+ el
          case UnitLiteral => Seq()
          case e2 => Seq(e2)
        }
        val fexpr = nexprs match {
          case Seq() => UnitLiteral
          case Seq(e) => e
          case es => Block(es.init, es.last).setType(es.last.getType)
        }
        Some(fexpr)
      }
      case _ => None
    }
    searchAndReplaceDFS(applyToTree)(expr)
  }

  //checking whether the expr is pure, that is do not contains any non-pure construct: assign, while, blocks, array, ...
  //this is expected to be true when entering the "backend" of Leon
  def isPure(expr: Expr): Boolean = {
    def convert(t: Expr) : Boolean = t match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case LetDef(_, _) => false
      case ArrayUpdate(_, _, _) => false
      case ArrayMake(_) => false
      case ArrayClone(_) => false
      case Epsilon(_) => false
      case _ => true
    }
    def combine(b1: Boolean, b2: Boolean) = b1 && b2
    def compute(e: Expr, b: Boolean) = e match {
      case Block(_, _) => false
      case Assignment(_, _) => false
      case While(_, _) => false
      case LetVar(_, _, _) => false
      case LetDef(_, _) => false
      case ArrayUpdate(_, _, _) => false
      case ArrayMake(_) => false
      case ArrayClone(_) => false
      case Epsilon(_) => false
      case _ => b
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def containsEpsilon(expr: Expr): Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case (l : Epsilon) => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case (l : Epsilon) => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def containsLetDef(expr: Expr): Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case (l : LetDef) => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case (l : LetDef) => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }
  def containsIfExpr(expr: Expr): Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case (i: IfExpr) => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case (i: IfExpr) => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def variablesOf(expr: Expr) : Set[Identifier] = {
    def convert(t: Expr) : Set[Identifier] = t match {
      case Variable(i) => Set(i)
      case _ => Set.empty
    }
    def combine(s1: Set[Identifier], s2: Set[Identifier]) = s1 ++ s2
    def compute(t: Expr, s: Set[Identifier]) = t match {
      case Let(i,_,_) => s -- Set(i)
      case MatchExpr(_, cses) => s -- (cses.map(_.pattern.binders).foldLeft(Set[Identifier]())((a, b) => a ++ b))
      case AnonymousFunctionInvocation(i,_) => s ++ Set[Identifier](i)
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def containsFunctionCalls(expr : Expr) : Boolean = {
    def convert(t : Expr) : Boolean = t match {
      case f : FunctionInvocation => true
      case _ => false
    }
    def combine(c1 : Boolean, c2 : Boolean) : Boolean = c1 || c2
    def compute(t : Expr, c : Boolean) = t match {
      case f : FunctionInvocation => true
      case _ => c
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def topLevelFunctionCallsOf(expr: Expr, barring : Set[FunDef] = Set.empty) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(fd, _) if(!barring(fd)) => Set(f)
      case _ => Set.empty
    }
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2
    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(fd,  _) if(!barring(fd)) => Set(f) // ++ s that's the difference with the one below
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def allNonRecursiveFunctionCallsOf(expr: Expr, program: Program) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(fd, _) if program.isRecursive(fd) => Set(f)
      case _ => Set.empty
    }
    
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2

    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(fd,_) if program.isRecursive(fd) => Set(f) ++ s
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def functionCallsOf(expr: Expr) : Set[FunctionInvocation] = {
    def convert(t: Expr) : Set[FunctionInvocation] = t match {
      case f @ FunctionInvocation(_, _) => Set(f)
      case _ => Set.empty
    }
    def combine(s1: Set[FunctionInvocation], s2: Set[FunctionInvocation]) = s1 ++ s2
    def compute(t: Expr, s: Set[FunctionInvocation]) = t match {
      case f @ FunctionInvocation(_, _) => Set(f) ++ s
      case _ => s
    }
    treeCatamorphism(convert, combine, compute, expr)
  }

  def contains(expr: Expr, matcher: Expr=>Boolean) : Boolean = {
    treeCatamorphism[Boolean](
      matcher,
      (b1: Boolean, b2: Boolean) => b1 || b2,
      (t: Expr, b: Boolean) => b || matcher(t),
      expr)
  }

  def allIdentifiers(expr: Expr) : Set[Identifier] = expr match {
    case l @ Let(binder, e, b) => allIdentifiers(e) ++ allIdentifiers(b) + binder
    case l @ LetVar(binder, e, b) => allIdentifiers(e) ++ allIdentifiers(b) + binder
    case l @ LetDef(fd, b) => allIdentifiers(fd.getBody) ++ allIdentifiers(b) + fd.id
    case n @ NAryOperator(args, _) =>
      (args map (TreeOps.allIdentifiers(_))).foldLeft(Set[Identifier]())((a, b) => a ++ b)
    case b @ BinaryOperator(a1,a2,_) => allIdentifiers(a1) ++ allIdentifiers(a2)
    case u @ UnaryOperator(a,_) => allIdentifiers(a)
    case i @ IfExpr(a1,a2,a3) => allIdentifiers(a1) ++ allIdentifiers(a2) ++ allIdentifiers(a3)
    case m @ MatchExpr(scrut, cses) =>
      (cses map (_.allIdentifiers)).foldLeft(Set[Identifier]())((a, b) => a ++ b) ++ allIdentifiers(scrut)
    case Variable(id) => Set(id)
    case t: Terminal => Set.empty
  }

  def allDeBruijnIndices(expr: Expr) : Set[DeBruijnIndex] =  {
    def convert(t: Expr) : Set[DeBruijnIndex] = t match {
      case i @ DeBruijnIndex(idx) => Set(i)
      case _ => Set.empty
    }
    def combine(s1: Set[DeBruijnIndex], s2: Set[DeBruijnIndex]) = s1 ++ s2
    treeCatamorphism(convert, combine, expr)
  }

  /* Simplifies let expressions:
   *  - removes lets when expression never occurs
   *  - simplifies when expressions occurs exactly once
   *  - expands when expression is just a variable.
   * Note that the code is simple but far from optimal (many traversals...)
   */
  def simplifyLets(expr: Expr) : Expr = {
    def simplerLet(t: Expr) : Option[Expr] = t match {
      case letExpr @ Let(i, t: Terminal, b) => Some(replace(Map((Variable(i) -> t)), b))
      case letExpr @ Let(i,e,b) => {
        val occurences = treeCatamorphism[Int]((e:Expr) => e match {
          case Variable(x) if x == i => 1
          case _ => 0
        }, (x:Int,y:Int)=>x+y, b)
        if(occurences == 0) {
          Some(b)
        } else if(occurences == 1) {
          Some(replace(Map((Variable(i) -> e)), b))
        } else {
          None
        }
      }
      //case letTuple @ LetTuple(ids, expr, body) if ids.size == 1 =>
      //  simplerLet(Let(ids.head, TupleSelect(expr, 1).setType(ids.head.getType), body))

      case letTuple @ LetTuple(ids, Tuple(exprs), body) =>

        var newBody = body

        val (remIds, remExprs) = (ids zip exprs).filter { 
          case (id, value: Terminal) =>
            newBody = replace(Map((Variable(id) -> value)), newBody)
            //we replace, so we drop old
            false
          case (id, value) =>
            val occurences = treeCatamorphism[Int]((e:Expr) => e match {
              case Variable(x) if x == id => 1
              case _ => 0
            }, (x:Int,y:Int)=>x+y, body)

            if(occurences == 0) {
              false
            } else if(occurences == 1) {
              newBody = replace(Map((Variable(id) -> value)), newBody)
              false
            } else {
              true
            }
        }.unzip


        if (remIds.isEmpty) {
          Some(newBody)
        } else if (remIds.tail.isEmpty) {
          Some(Let(remIds.head, remExprs.head, newBody))
        } else {
          Some(LetTuple(remIds, Tuple(remExprs), newBody))
        }
      case _ => None 
    }
    searchAndReplaceDFS(simplerLet)(expr)
  }

  // Pulls out all let constructs to the top level, and makes sure they're
  // properly ordered.
  private type DefPair  = (Identifier,Expr) 
  private type DefPairs = List[DefPair] 
  private def allLetDefinitions(expr: Expr) : DefPairs = treeCatamorphism[DefPairs](
    (e: Expr) => Nil,
    (s1: DefPairs, s2: DefPairs) => s1 ::: s2,
    (e: Expr, dps: DefPairs) => e match {
      case Let(i, e, _) => (i,e) :: dps
      case _ => dps
    },
    expr)
  
  private def killAllLets(expr: Expr) : Expr = searchAndReplaceDFS((e: Expr) => e match {
    case Let(_,_,ex) => Some(ex)
    case _ => None
  })(expr)

  def liftLets(expr: Expr) : Expr = {
    val initialDefinitionPairs = allLetDefinitions(expr)
    val definitionPairs = initialDefinitionPairs.map(p => (p._1, killAllLets(p._2)))
    val occursLists : Map[Identifier,Set[Identifier]] = Map(definitionPairs.map((dp: DefPair) => (dp._1 -> variablesOf(dp._2).toSet.filter(_.isLetBinder))) : _*)
    var newList : DefPairs = Nil
    var placed  : Set[Identifier] = Set.empty
    val toPlace = definitionPairs.size
    var placedC = 0
    var traversals = 0

    while(placedC < toPlace) {
      if(traversals > toPlace + 1) {
        scala.sys.error("Cycle in let definitions or multiple definition for the same identifier in liftLets : " + definitionPairs.mkString("\n"))
      }
      for((id,ex) <- definitionPairs) if (!placed(id)) {
        if((occursLists(id) -- placed) == Set.empty) {
          placed = placed + id
          newList = (id,ex) :: newList
          placedC = placedC + 1
        }
      }
      traversals = traversals + 1
    }

    val noLets = killAllLets(expr)

    val res = (newList.foldLeft(noLets)((e,iap) => Let(iap._1, iap._2, e)))
    simplifyLets(res)
  }

  def wellOrderedLets(tree : Expr) : Boolean = {
    val pairs = allLetDefinitions(tree)
    val definitions: Set[Identifier] = Set(pairs.map(_._1) : _*)
    val vars: Set[Identifier] = variablesOf(tree)
    val intersection = vars intersect definitions
    if(!intersection.isEmpty) {
      intersection.foreach(id => {
        Settings.reporter.error("Variable with identifier '" + id + "' has escaped its let-definition !")
      })
      false
    } else {
      vars.forall(id => if(id.isLetBinder) {
        Settings.reporter.error("Variable with identifier '" + id + "' has lost its let-definition (it disappeared??)")
        false
      } else {
        true
      })
    }
  }

  /* Fully expands all let expressions. */
  def expandLets(expr: Expr) : Expr = {
    def rec(ex: Expr, s: Map[Identifier,Expr]) : Expr = ex match {
      case v @ Variable(id) if s.isDefinedAt(id) => rec(s(id), s)
      case l @ Let(i,e,b) => rec(b, s + (i -> rec(e, s)))
      case i @ IfExpr(t1,t2,t3) => IfExpr(rec(t1, s),rec(t2, s),rec(t3, s)).setType(i.getType)
      case m @ MatchExpr(scrut,cses) => MatchExpr(rec(scrut, s), cses.map(inCase(_, s))).setType(m.getType).setPosInfo(m)
      case n @ NAryOperator(args, recons) => {
        var change = false
        val rargs = args.map(a => {
          val ra = rec(a, s)
          if(ra != a) {
            change = true  
            ra
          } else {
            a
          }            
        })
        if(change)
          recons(rargs).setType(n.getType)
        else
          n
      }
      case b @ BinaryOperator(t1,t2,recons) => {
        val r1 = rec(t1, s)
        val r2 = rec(t2, s)
        if(r1 != t1 || r2 != t2)
          recons(r1,r2).setType(b.getType)
        else
          b
      }
      case u @ UnaryOperator(t,recons) => {
        val r = rec(t, s)
        if(r != t)
          recons(r).setType(u.getType)
        else
          u
      }
      case t if t.isInstanceOf[Terminal] => t
      case unhandled => scala.sys.error("Unhandled case in expandLets: " + unhandled)
    }

    def inCase(cse: MatchCase, s: Map[Identifier,Expr]) : MatchCase = cse match {
      case SimpleCase(pat, rhs) => SimpleCase(pat, rec(rhs, s))
      case GuardedCase(pat, guard, rhs) => GuardedCase(pat, rec(guard, s), rec(rhs, s))
    }

    rec(expr, Map.empty)
  }

  private var matchConverterCache = new scala.collection.mutable.HashMap[Expr,Expr]()
  /** Rewrites all pattern-matching expressions into if-then-else expressions,
   * with additional error conditions. Does not introduce additional variables.
   * We use a cache because we can. */
  def matchToIfThenElse(expr: Expr) : Expr = {
    val toRet = if(matchConverterCache.isDefinedAt(expr)) {
      matchConverterCache(expr)
    } else {
      val converted = convertMatchToIfThenElse(expr)
      matchConverterCache(expr) = converted
      converted
    }

    toRet
  }

  def conditionForPattern(in: Expr, pattern: Pattern) : Expr = pattern match {
    case WildcardPattern(_) => BooleanLiteral(true)
    case InstanceOfPattern(_,_) => scala.sys.error("InstanceOfPattern not yet supported.")
    case CaseClassPattern(_, ccd, subps) => {
      assert(ccd.fields.size == subps.size)
      val pairs = ccd.fields.map(_.id).toList zip subps.toList
      val subTests = pairs.map(p => conditionForPattern(CaseClassSelector(ccd, in, p._1), p._2))
      val together = And(subTests)
      And(CaseClassInstanceOf(ccd, in), together)
    }
    case TuplePattern(_, subps) => {
      val TupleType(tpes) = in.getType
      assert(tpes.size == subps.size)
      val subTests = subps.zipWithIndex.map{case (p, i) => conditionForPattern(TupleSelect(in, i+1).setType(tpes(i)), p)}
      And(subTests)
    }
  }

  private def convertMatchToIfThenElse(expr: Expr) : Expr = {
    def mapForPattern(in: Expr, pattern: Pattern) : Map[Identifier,Expr] = pattern match {
      case WildcardPattern(None) => Map.empty
      case WildcardPattern(Some(id)) => Map(id -> in)
      case InstanceOfPattern(None, _) => Map.empty
      case InstanceOfPattern(Some(id), _) => Map(id -> in)
      case CaseClassPattern(b, ccd, subps) => {
        assert(ccd.fields.size == subps.size)
        val pairs = ccd.fields.map(_.id).toList zip subps.toList
        val subMaps = pairs.map(p => mapForPattern(CaseClassSelector(ccd, in, p._1), p._2))
        val together = subMaps.foldLeft(Map.empty[Identifier,Expr])(_ ++ _)
        b match {
          case Some(id) => Map(id -> in) ++ together
          case None => together
        }
      }
      case TuplePattern(b, subps) => {
        val TupleType(tpes) = in.getType
        assert(tpes.size == subps.size)

        val maps = subps.zipWithIndex.map{case (p, i) => mapForPattern(TupleSelect(in, i+1).setType(tpes(i)), p)}
        val map = maps.foldLeft(Map.empty[Identifier,Expr])(_ ++ _)
        b match {
          case Some(id) => map + (id -> in)
          case None => map
        }
      }
    }

    def rewritePM(e: Expr) : Option[Expr] = e match {
      case m @ MatchExpr(scrut, cases) => {
        // println("Rewriting the following PM: " + e)

        val condsAndRhs = for(cse <- cases) yield {
          val map = mapForPattern(scrut, cse.pattern)
          val patCond = conditionForPattern(scrut, cse.pattern)
          val realCond = cse.theGuard match {
            case Some(g) => And(patCond, replaceFromIDs(map, g))
            case None => patCond
          }
          val newRhs = replaceFromIDs(map, cse.rhs)
          (realCond, newRhs)
        } 

        val optCondsAndRhs = if(SimplePatternMatching.isSimple(m)) {
          // this is a hackish optimization: because we know all cases are covered, we replace the last condition by true (and that drops the check)
          val lastExpr = condsAndRhs.last._2

          condsAndRhs.dropRight(1) ++ Seq((BooleanLiteral(true),lastExpr))
        } else {
          condsAndRhs
        }

        val bigIte = optCondsAndRhs.foldRight[Expr](Error("non-exhaustive match").setType(bestRealType(m.getType)).setPosInfo(m))((p1, ex) => {
          if(p1._1 == BooleanLiteral(true)) {
            p1._2
          } else {
            IfExpr(p1._1, p1._2, ex).setType(m.getType)
          }
        })

        Some(bigIte)
      }
      case _ => None
    }
    
    searchAndReplaceDFS(rewritePM)(expr)
  }

  private var mapGetConverterCache = new scala.collection.mutable.HashMap[Expr,Expr]()
  /** Rewrites all map accesses with additional error conditions. */
  def mapGetWithChecks(expr: Expr) : Expr = {
    val toRet = if (mapGetConverterCache.isDefinedAt(expr)) {
      mapGetConverterCache(expr)
    } else {
      val converted = convertMapGet(expr)
      mapGetConverterCache(expr) = converted
      converted
    }

    toRet
  }

  private def convertMapGet(expr: Expr) : Expr = {
    def rewriteMapGet(e: Expr) : Option[Expr] = e match {
      case mg @ MapGet(m,k) => 
        val ida = MapIsDefinedAt(m, k)
        Some(IfExpr(ida, mg, Error("key not found for map access").setType(mg.getType).setPosInfo(mg)).setType(mg.getType))
      case _ => None
    }

    searchAndReplaceDFS(rewriteMapGet)(expr)
  }

  // prec: expression does not contain match expressions
  def measureADTChildrenDepth(expression: Expr) : Int = {
    import scala.math.max

    def rec(ex: Expr, lm: Map[Identifier,Int]) : Int = ex match {
      case Let(i,e,b) => rec(b,lm + (i -> rec(e,lm)))
      case Variable(id) => lm.getOrElse(id, 0)
      case CaseClassSelector(_, e, _) => rec(e,lm) + 1
      case NAryOperator(args, _) => if(args.isEmpty) 0 else args.map(rec(_,lm)).max
      case BinaryOperator(e1,e2,_) => max(rec(e1,lm), rec(e2,lm))
      case UnaryOperator(e,_) => rec(e,lm)
      case IfExpr(c,t,e) => max(max(rec(c,lm),rec(t,lm)),rec(e,lm))
      case t: Terminal => 0
      case _ => scala.sys.error("Not handled in measureChildrenDepth : " + ex)
    }
    
    rec(expression,Map.empty)
  }

  private val random = new scala.util.Random()

  def randomValue(v: Variable) : Expr = randomValue(v.getType)
  def simplestValue(v: Variable) : Expr = simplestValue(v.getType)

  def randomValue(tpe: TypeTree) : Expr = tpe match {
    case Int32Type => IntLiteral(random.nextInt(42))
    case BooleanType => BooleanLiteral(random.nextBoolean())
    case AbstractClassType(acd) =>
      val children = acd.knownChildren
      randomValue(classDefToClassType(children(random.nextInt(children.size))))
    case CaseClassType(cd) =>
      val fields = cd.fields
      CaseClass(cd, fields.map(f => randomValue(f.getType)))
    case _ => throw new Exception("I can't choose random value for type " + tpe)
  }

  def simplestValue(tpe: TypeTree) : Expr = tpe match {
    case Int32Type => IntLiteral(0)
    case BooleanType => BooleanLiteral(false)
    case AbstractClassType(acd) => {
      val children = acd.knownChildren
      val simplerChildren = children.filter{
        case ccd @ CaseClassDef(id, Some(parent), fields) =>
          !fields.exists(vd => vd.getType match {
            case AbstractClassType(fieldAcd) => acd == fieldAcd
            case CaseClassType(fieldCcd) => ccd == fieldCcd
            case _ => false
          })
        case _ => false
      }
      def orderByNumberOfFields(fst: ClassTypeDef, snd: ClassTypeDef) : Boolean = (fst, snd) match {
        case (CaseClassDef(_, _, flds1), CaseClassDef(_, _, flds2)) => flds1.size <= flds2.size
        case _ => true
      }
      val orderedChildren = simplerChildren.sortWith(orderByNumberOfFields)
      simplestValue(classDefToClassType(orderedChildren.head))
    }
    case CaseClassType(ccd) =>
      val fields = ccd.fields
      CaseClass(ccd, fields.map(f => simplestValue(f.getType)))
    case SetType(baseType) => EmptySet(baseType).setType(tpe)
    case MapType(fromType, toType) => EmptyMap(fromType, toType).setType(tpe)
    case FunctionType(fromTypes, toType) => AnonymousFunction(Seq.empty, simplestValue(toType)).setType(tpe)
    case _ => throw new Exception("I can't choose simplest value for type " + tpe)
  }

  //guarentee that all IfExpr will be at the top level and as soon as you encounter a non-IfExpr, then no more IfExpr can be find in the sub-expressions
  //require no-match, no-ets and only pure code
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(IfExpr(c, t, e), op) => Some(IfExpr(c, op(t).setType(uop.getType), op(e).setType(uop.getType)).setType(uop.getType))
      case bop@BinaryOperator(IfExpr(c, t, e), t2, op) => Some(IfExpr(c, op(t, t2).setType(bop.getType), op(e, t2).setType(bop.getType)).setType(bop.getType))
      case bop@BinaryOperator(t1, IfExpr(c, t, e), op) => Some(IfExpr(c, op(t1, t).setType(bop.getType), op(t1, e).setType(bop.getType)).setType(bop.getType))
      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).setType(nop.getType),
            op(beforeIte ++ Seq(e) ++ afterIte).setType(nop.getType)
          ).setType(nop.getType))
        }
      }
      case _ => None
    }

    def fix[A](f: (A) => A, a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f, na)
    }
    fix(searchAndReplaceDFS(transform), expr)
  }

  def genericTransform[C](pre:  (Expr, C) => (Expr, C),
                          post: (Expr, C) => (Expr, C),
                          combiner: (Expr, C, Seq[C]) => C)(init: C)(expr: Expr) = {

    def rec(eIn: Expr, cIn: C): (Expr, C) = {

      val (expr, ctx) = pre(eIn, cIn)

      val (newExpr, newC) = expr match {
        case t: Terminal =>
          (expr, ctx)

        case UnaryOperator(e, builder) =>
          val (e1, c) = rec(e, ctx)
          val newE = builder(e1)

          (newE, combiner(newE, ctx, Seq(c)))

        case BinaryOperator(e1, e2, builder) =>
          val (ne1, c1) = rec(e1, ctx)
          val (ne2, c2) = rec(e2, ctx)
          val newE = builder(ne1, ne2)

          (newE, combiner(newE, ctx, Seq(c1, c2)))

        case NAryOperator(es, builder) =>
          val (nes, cs) = es.map(e => rec(e, ctx)).unzip
          val newE = builder(nes)

          (newE, combiner(newE, ctx, cs))

        case e =>
          sys.error("Expression "+e+" ["+e.getClass+"] is not extractable")
      }

      post(newExpr, newC)
    }

    rec(expr, init)
  }

  private def noCombiner[C](e: Expr, initC: C, subCs: Seq[C]) = initC

  def simpleTransform(pre: Expr => Expr, post: Expr => Expr)(expr: Expr) = {
    val newPre  = (e: Expr, c: Unit) => (pre(e), ())
    val newPost = (e: Expr, c: Unit) => (post(e), ())

    genericTransform[Unit](newPre, newPost, noCombiner)(())(expr)._1
  }

  def simplePreTransform(pre: Expr => Expr)(expr: Expr) = {
    val newPre  = (e: Expr, c: Unit) => (pre(e), ())

    genericTransform[Unit](newPre, (_, _), noCombiner)(())(expr)._1
  }

  def simplePostTransform(post: Expr => Expr)(expr: Expr) = {
    val newPost = (e: Expr, c: Unit) => (post(e), ())

    genericTransform[Unit]((_, _), newPost, noCombiner)(())(expr)._1
  }

  def toDNF(e: Expr): Expr = {
    def pre(e: Expr) = e match {
      case And(Seq(l, Or(Seq(r1, r2)))) =>
        Or(And(l, r1), And(l, r2))
      case And(Seq(Or(Seq(l1, l2)), r)) =>
        Or(And(l1, r), And(l2, r))
      case _ =>
        e
    }

    simplePreTransform(pre)(e)
  }

  def toCNF(e: Expr): Expr = {
    def pre(e: Expr) = e match {
      case Or(Seq(l, And(Seq(r1, r2)))) =>
        And(Or(l, r1), Or(l, r2))
      case Or(Seq(And(Seq(l1, l2)), r)) =>
        And(Or(l1, r), Or(l2, r))
      case _ =>
        e
    }

    simplePreTransform(pre)(e)
  }

  /*
   * Transforms complicated Ifs into multiple nested if blocks
   * It will decompose every OR clauses, and it will group AND clauses checking
   * isInstanceOf toghether.
   *
   *  if (a.isInstanceof[T1] && a.tail.isInstanceof[T2] && a.head == a2 || C) {
   *     T
   *  } else {
   *     E
   *  }
   *
   * Becomes:
   *
   *  if (a.isInstanceof[T1] && a.tail.isInstanceof[T2]) {
   *    if (a.head == a2) {
   *      T
   *    } else {
   *      if(C) {
   *        T
   *      } else {
   *        E
   *      }
   *    }
   *  } else {
   *    if(C) {
   *      T
   *    } else {
   *      E
   *    }
   *  }
   * 
   * This transformation runs immediately before patternMatchReconstruction.
   */
  def decomposeIfs(e: Expr): Expr = {
    def pre(e: Expr): Expr = e match {
      case IfExpr(cond, then, elze) =>
        val TopLevelOrs(orcases) = toDNF(cond)

        if (!orcases.tail.isEmpty) {
          pre(IfExpr(orcases.head, then, IfExpr(Or(orcases.tail), then, elze)))
        } else {
          val TopLevelAnds(andcases) = orcases.head

          val (andis, andnotis) = andcases.partition(_.isInstanceOf[CaseClassInstanceOf])

          if (andis.isEmpty || andnotis.isEmpty) {
            e
          } else {
            IfExpr(And(andis), IfExpr(And(andnotis), then, elze), elze)
          }
        }
      case _ =>
        e
    }

    simplePreTransform(pre)(e)
  }

  // This transformation assumes IfExpr of the form generated by decomposeIfs
  def patternMatchReconstruction(e: Expr): Expr = {
    def pre(e: Expr): Expr = e match {
      case IfExpr(cond, then, elze) =>
        val TopLevelAnds(cases) = cond

        if (cases.forall(_.isInstanceOf[CaseClassInstanceOf])) {
          // matchingOn might initially be: a : T1, a.tail : T2, b: T2
          def selectorDepth(e: Expr): Int = e match {
            case v: Variable =>
              0
            case cd: CaseClassSelector =>
              1+selectorDepth(cd.caseClass)
          }

          var scrutSet = Set[Expr]()
          var conditions = Map[Expr, CaseClassDef]()

          var matchingOn = cases.collect { case cc : CaseClassInstanceOf => cc } sortBy(cc => selectorDepth(cc.expr))
          for (CaseClassInstanceOf(cd, expr) <- matchingOn) {
            conditions += expr -> cd

            expr match {
              case v: Variable =>
                scrutSet += v 
              case cd: CaseClassSelector =>
                if (!scrutSet.contains(cd.caseClass)) {
                  // we found a test looking like "a.foo.isInstanceof[..]"
                  // without a check on "a".
                  scrutSet += cd
                }
            }
          }

          var substMap = Map[Expr, Expr]()


          def computePatternFor(cd: CaseClassDef, prefix: Expr): Pattern = {

            val id = prefix match {
              case CaseClassSelector(_, _, id) => id
              case Variable(id) => id
            }

            val binder = FreshIdentifier(id.name, true).setType(id.getType) // Is it full of women though?

            // prefix becomes binder
            substMap += prefix -> Variable(binder)
            substMap += CaseClassInstanceOf(cd, prefix) -> BooleanLiteral(true)

            val subconds = for (id <- cd.fieldsIds) yield {
              val fieldSel = CaseClassSelector(cd, prefix, id)
              if (conditions contains fieldSel) {
                computePatternFor(conditions(fieldSel), fieldSel)
              } else {
                val b = FreshIdentifier(id.name, true).setType(id.getType)
                substMap += fieldSel -> Variable(b)
                WildcardPattern(Some(b))
              }
            }

            CaseClassPattern(Some(binder), cd, subconds)
          }

          val (scrutinees, patterns) = scrutSet.toSeq.map(s => (s, computePatternFor(conditions(s), s))) unzip

          val (scrutinee, pattern) = if (scrutinees.size > 1) {
            (Tuple(scrutinees), TuplePattern(None, patterns))
          } else {
            (scrutinees.head, patterns.head)
          }

          // We use searchAndReplace to replace the biggest match first
          // (topdown).
          // So replaceing using Map(a => b, CC(a) => d) will replace
          // "CC(a)" by "d" and not by "CC(b)"
          val newThen = searchAndReplace(substMap.get)(then)

          MatchExpr(scrutinee, Seq(SimpleCase(pattern, newThen), SimpleCase(WildcardPattern(None), elze)))
        } else {
          e
        }
      case _ =>
        e
    }

    simplePreTransform(pre)(e)
  }

  def simplifyTautologies(solver : Solver)(expr : Expr) : Expr = {
    def pre(e : Expr) = e match {
      case IfExpr(cond, then, elze) => solver.solve(cond) match {
        case Some(true)  => then
        case Some(false) => solver.solve(Not(cond)) match {
          case Some(true) => elze
          case _ => e
        }
        case None => e
      }
      case _ => e
    }

    simplePreTransform(pre)(expr)
  }
}
