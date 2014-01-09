package leon
package termination

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.purescala.TypeTrees._
import leon.purescala.TypeTreeOps._
import leon.purescala.Common._

import scala.collection.mutable.{Map => MutableMap}

final case class Chain(chain: List[Relation]) {

  private def identifier: Set[(Relation, Relation)] = (chain zip (chain.tail :+ chain.head)).toSet

  override def equals(obj: Any): Boolean = obj match {
    case (chain : Chain) => chain.identifier == identifier
    case _ => false
  }

  override def hashCode(): Int = identifier.hashCode

  def funDef  : FunDef      = chain.head.funDef
  def funDefs : Set[FunDef] = chain.map(_.funDef).toSet

  lazy val size: Int = chain.size

  def loop(initialSubst: Map[Identifier, Expr] = Map(), finalSubst: Map[Identifier, Expr] = Map()) : Seq[Expr] = {
    ChainBuilder.loopOption(funDef, chain, initialSubst = initialSubst, finalSubst = finalSubst).get
  }

  def reentrant(other: Chain) : Seq[Expr] = {
    assert(funDef == other.funDef)
    val bindingSubst : Map[Identifier, Expr] = funDef.args.map({
      arg => arg.id -> arg.id.freshen.toVariable
    }).toMap
    val firstLoop = loop(finalSubst = bindingSubst)
    val secondLoop = other.loop(initialSubst = bindingSubst)
    firstLoop ++ secondLoop
  }

  def inlined: TraversableOnce[Expr] = {
    def rec(list: List[Relation], tpSubst: Map[TypeParameter, TypeTree], idSubst: Map[Identifier, Expr]): List[Expr] = list match {
      case Relation(_, _, fi @ FunctionInvocation(_, args), _) :: xs =>
        val invocation = replaceTypesInExpr(tpSubst, idSubst, fi).asInstanceOf[FunctionInvocation]
        val mappedArgs = args.map(replaceTypesInExpr(tpSubst, idSubst, _))
        val newIdSubst = invocation.typed.args.map(_.id).zip(mappedArgs).toMap
        // We assume we have a body at this point. It would be weird to have gotten here without one...
        val expr = hoistIte(expandLets(matchToIfThenElse(invocation.typed.body.get)))
        val inlinedExpr = replaceTypesInExpr(invocation.tpSubst, newIdSubst, expr)
        inlinedExpr:: rec(xs, invocation.tpSubst, newIdSubst)
      case Nil => Nil
    }

    val body = hoistIte(expandLets(matchToIfThenElse(funDef.body.get)))
    body :: rec(chain, Map.empty, funDef.args.map(arg => arg.id -> arg.toVariable).toMap)
  }
}

object ChainBuilder {
  private[termination] def loopOption(funDef       : FunDef,
                                      relations    : List[Relation],
                                      initialSubst : Map[Identifier, Expr] = Map.empty,
                                      finalSubst   : Map[Identifier, Expr] = Map.empty) : Option[Seq[Expr]] = {
    def rec(relations: List[Relation], tpSubst: Map[TypeParameter, TypeTree], subst: Map[Identifier, Expr]): Option[Seq[Expr]] = relations match {
      case Relation(_, path, fi @ FunctionInvocation(fd, args), _) :: Nil =>
        if (fi.typed != TypedFunDef(funDef)) None else {
          val newPath = path.map(replaceTypesInExpr(tpSubst, subst, _))
          val equalityConstraints = if (finalSubst.isEmpty) Seq() else {
            val newArgs = args.map(replaceTypesInExpr(tpSubst, subst, _))
            (fd.args.map(arg => finalSubst(arg.id)) zip newArgs).map(p => Equals(p._1, p._2))
          }
          Some(newPath ++ equalityConstraints)
        }
      case Relation(_, path, fi @ FunctionInvocation(fd, args), _) :: xs =>
        val (newPath, newArgs) = (path.map(replaceTypesInExpr(tpSubst, subst, _)), args.map(replaceTypesInExpr(tpSubst, subst, _)))
        val invocation = replaceTypesInExpr(tpSubst, subst, fi).asInstanceOf[FunctionInvocation]
        val formalArgs = fd.args.map(_.id)
        val nextArgVars = invocation.typed.args.map(vd => vd.id.freshen.toVariable)
        lazy val constraints = newPath ++ (nextArgVars zip newArgs).map(p => Equals(p._1, p._2))
        rec(xs, invocation.tpSubst, (formalArgs zip nextArgVars).toMap).map {
          tailConstraints => constraints ++ tailConstraints
        }
      case Nil => sys.error("Empty chain shouldn't exist by construction")
    }

    val subst : Map[Identifier, Expr] = if (initialSubst.nonEmpty) initialSubst else {
      funDef.args.map(arg => arg.id -> arg.toVariable).toMap
    }

    rec(relations, Map.empty, subst)
  }
}

trait ChainBuilder extends RelationBuilder { self: TerminationChecker with Strengthener with RelationComparator =>
  import ChainBuilder._

  protected type ChainSignature = (FunDef, Set[RelationSignature])

  protected def funDefChainSignature(funDef: FunDef): ChainSignature = {
    funDef -> (self.program.transitiveCallees(funDef) + funDef).map(funDefRelationSignature(_))
  }

  private val chainCache : MutableMap[FunDef, (Set[Chain], ChainSignature)] = MutableMap.empty

  def getChains(funDef: FunDef)(implicit solver: Processor with Solvable): Set[Chain] = chainCache.get(funDef) match {
    case Some((chains, signature)) if signature == funDefChainSignature(funDef) => chains
    case _ => {
      val relationConstraints : MutableMap[Relation, SizeConstraint] = MutableMap.empty

      def decreasing(relations: List[Relation]): Boolean = {
        val constraints = relations.map(relation => relationConstraints.get(relation).getOrElse {
          val Relation(funDef, path, FunctionInvocation(fd, args), _) = relation
          val (e1, e2) = (Tuple(funDef.args.map(_.toVariable)), Tuple(args))
          val constraint = if (solver.definitiveALL(Implies(And(path), self.softDecreasing(e1, e2)), funDef.precondition)) {
            if (solver.definitiveALL(Implies(And(path), self.sizeDecreasing(e1, e2)), funDef.precondition)) {
              StrongDecreasing
            } else {
              WeakDecreasing
            }
          } else {
            NoConstraint
          }

          relationConstraints(relation) = constraint
          constraint
        }).toSet

        !constraints(NoConstraint) && constraints(StrongDecreasing)
      }

      def chains(partials: List[(Relation, List[Relation])], results: Set[Chain]) : Set[Chain] = partials.foldLeft(results) {
        case (results, (first, chain @ Relation(_, _, FunctionInvocation(fd, _), _) :: xs)) =>
          val relations = getRelations(fd)

          if (!self.program.transitivelyCalls(fd, funDef)) results else {
            val rChain = chain.reverse // we're working on reversed chains
            lazy val loop = loopOption(fd, rChain)
            val (continue, result) = if (
                !decreasing(rChain) && // chain is irrelevant if guaranteed decreasing
                relations.contains(first) && // chain is not a true chain if it can't fall back on first
                loop.isDefined && // make sure this is a real chain (ie. we can create a loop with its relations)
                !results(Chain(rChain))) { // chains may be computed multiple times because of self-recursion, so don't add dupplicates
              if (solver.maybeSAT(And(loop.get), funDef.precondition)) { // test if chain path is in SAT
                true -> Some(Chain(rChain))
              } else {
                false -> None
              }
            } else {
              true -> None
            }

            val newResults = results ++ result

            if (continue) {
              // Partial chains can fall back onto a transition that was already taken (thus creating a cycle
              // inside the chain). Since this cycle will be discovered elsewhere, such partial chains should be
              // dropped from the partial chain list
              val transitions = relations -- chain.toSet
              val nextPartials = transitions.map(transition => (first, transition :: chain)).toList
              chains(nextPartials, newResults)
            } else {
              newResults
            }
          }
        case (_, (_, Nil)) => scala.sys.error("Empty partial chain shouldn't exist by construction")
      }

      val initialPartials = getRelations(funDef).map(r => (r, r :: Nil)).toList
      val result = chains(initialPartials, Set.empty)

      chainCache(funDef) = (result, funDefChainSignature(funDef))

      result
    }
  }
}
