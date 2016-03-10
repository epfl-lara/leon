package leon
package laziness

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Types._
import purescala.TypeOps._
import invariant.util.TypeUtil._

object TypeChecker {
   /**
   * `gamma` is the initial type environment which has
   * type bindings for free variables of `ine`.
   * It is not necessary that gamma should match the types of the
   * identifiers of the free variables.
   * Set and Maps are not supported yet
   */
  def inferTypesOfLocals(ine: Expr, initGamma: Map[Identifier, TypeTree]): Expr = {
    var idmap = Map[Identifier, Identifier]()
    var gamma = initGamma

    /**
     * Note this method has side-effects
     */
    def makeIdOfType(oldId: Identifier, tpe: TypeTree): Identifier = {
      if (oldId.getType != tpe) {
        val freshid = FreshIdentifier(oldId.name, tpe, true)
        idmap += (oldId -> freshid)
        gamma += (oldId -> tpe)
        freshid
      } else oldId
    }

    def rec(e: Expr): (TypeTree, Expr) = {
      val res = e match {
        case Let(id, value, body) =>
          val (valType, nval) = rec(value)
          val nid = makeIdOfType(id, valType)
          val (btype, nbody) = rec(body)
          (btype, Let(nid, nval, nbody))

        case Ensuring(body, Lambda(Seq(resdef @ ValDef(resid)), postBody)) =>
          body match {
            case NoTree(tpe) =>
              val nres = makeIdOfType(resid, tpe)
              (tpe, Ensuring(body, Lambda(Seq(ValDef(nres)), rec(postBody)._2)))
            case _ =>
              val (btype, nbody) = rec(body)
              val nres = makeIdOfType(resid, btype)
              (btype, Ensuring(nbody, Lambda(Seq(ValDef(nres)), rec(postBody)._2)))
          }

        case MatchExpr(scr, mcases) =>
          val (scrtype, nscr) = rec(scr)
          val ncases = mcases.map {
            case MatchCase(pat, optGuard, rhs) =>
              // resetting the type of patterns in the matches
              def mapPattern(p: Pattern, expType: TypeTree): (Pattern, TypeTree) = {
                p match {
                  case InstanceOfPattern(bopt, ict) =>
                    // choose the subtype of the `expType` that
                    // has the same constructor as `ict`
                    val ntype = subcast(ict, expType.asInstanceOf[ClassType])
                    if (!ntype.isDefined)
                      throw new IllegalStateException(s"Cannot find subtype of $expType with name: ${ict.classDef.id.toString}")
                    val nbopt = bopt.map(makeIdOfType(_, ntype.get))
                    (InstanceOfPattern(nbopt, ntype.get), ntype.get)

                  case CaseClassPattern(bopt, ict, subpats) =>
                    val ntype = subcast(ict, expType.asInstanceOf[ClassType])
                    if (!ntype.isDefined)
                      throw new IllegalStateException(s"Cannot find subtype of $expType with name: ${ict.classDef.id.toString}")
                    val cct = ntype.get.asInstanceOf[CaseClassType]
                    val nbopt = bopt.map(makeIdOfType(_, cct))
                    val npats = (subpats zip cct.fieldsTypes).map {
                      case (p, t) =>
                        //println(s"Subpat: $p expected type: $t")
                        mapPattern(p, t)._1
                    }
                    (CaseClassPattern(nbopt, cct, npats), cct)

                  case TuplePattern(bopt, subpats) =>
                    val TupleType(subts) = expType
                    val patnTypes = (subpats zip subts).map {
                      case (p, t) => mapPattern(p, t)
                    }
                    val npats = patnTypes.map(_._1)
                    val ntype = TupleType(patnTypes.map(_._2))
                    val nbopt = bopt.map(makeIdOfType(_, ntype))
                    (TuplePattern(nbopt, npats), ntype)

                  case WildcardPattern(bopt) =>
                    val nbopt = bopt.map(makeIdOfType(_, expType))
                    (WildcardPattern(nbopt), expType)

                  case LiteralPattern(bopt, lit) =>
                    val ntype = lit.getType
                    val nbopt = bopt.map(makeIdOfType(_, ntype))
                    (LiteralPattern(nbopt, lit), ntype)
                  case _ =>
                    throw new IllegalStateException("Not supported yet!")
                }
              }
              val npattern = mapPattern(pat, scrtype)._1
              val nguard = optGuard.map(rec(_)._2)
              val nrhs = rec(rhs)._2
              //println(s"New rhs: $nrhs inferred type: ${nrhs.getType}")
              MatchCase(npattern, nguard, nrhs)
          }
          val nmatch = MatchExpr(nscr, ncases)
          //println("Old match expr: "+e+" \n new expr: "+nmatch)
          (nmatch.getType, nmatch)

        case cs @ CaseClassSelector(cltype, clExpr, fld) =>
          val (ncltype: ClassType, nclExpr) = rec(clExpr)
          // this is a hack. TODO: fix this
          subcast(cltype, ncltype) match {
            case Some(ntype : CaseClassType) =>
              val nop = CaseClassSelector(ntype, nclExpr, fld)
              (nop.getType, nop)
            case  _ =>
              throw new IllegalStateException(s"$nclExpr : $ncltype cannot be cast to case class type: $cltype")
          }

        case AsInstanceOf(clexpr, cltype) =>
          val (ncltype: ClassType, nexpr) = rec(clexpr)
          subcast(cltype, ncltype) match {
            case Some(ntype) => (ntype, AsInstanceOf(nexpr, ntype))
            case _ =>
              //println(s"asInstanceOf type of $clExpr is: $cltype inferred type of $nclExpr : $ct")
              throw new IllegalStateException(s"$nexpr : $ncltype cannot be cast to case class type: $cltype")
          }

        case v @ Variable(id) =>
          if (gamma.contains(id)) {
            if (idmap.contains(id))
              (gamma(id), idmap(id).toVariable)
            else {
              (gamma(id), v)
            }
          } else (id.getType, v)

        case FunctionInvocation(TypedFunDef(fd, tparams), args) =>
          //println(s"Consider expr: $e initial type: ${e.getType}")
          val nargs = args.map(arg => rec(arg)._2)
          var tpmap = Map[TypeParameter, TypeTree]()
          (fd.params zip nargs).foreach { x =>
              (x._1.getType, x._2.getType) match {
                case (t1, t2) =>
                  getTypeArguments(t1) zip getTypeArguments(t2) foreach {
                    case (tf : TypeParameter, ta) =>
                      tpmap += (tf -> ta)
                    case _ => ;
                  }
                /*throw new IllegalStateException(s"Types of formal and actual parameters: ($tf, $ta)"
                    + s"do not match for call: $call")*/
              }
            }
          // for uninterpreted functions, we could have a type parameter used only in the return type
          val dummyTParam = TypeParameter.fresh("R@")
          val ntparams = fd.tparams.map(_.tp).zipAll(tparams, dummyTParam, dummyTParam).map{
            case (paramt, argt) =>
              tpmap.getOrElse(paramt /* in this case we inferred the type parameter */,
                  argt /* in this case we reuse the argument type parameter */ )
          }
          val nexpr = FunctionInvocation(TypedFunDef(fd, ntparams), nargs)
          if (nexpr.getType == Untyped) {
            throw new IllegalStateException(s"Cannot infer type for expression: $e "+
                s"arg types: ${nargs.map(_.getType).mkString(",")} \n Callee: ${fd} \n caller: ${nexpr}")
          }
          (nexpr.getType, nexpr)

        case FiniteSet(els, baseType) =>
          val nels = els.map(rec(_)._2)
          // make sure every element has the same type (upcast it to the rootType)
          val nbaseType  = bestRealType(nels.head.getType)
          if(!nels.forall(el => bestRealType(el.getType) == nbaseType))
            throw new IllegalStateException("Not all elements in the set have the same type: "+nbaseType)
          val nop = FiniteSet(nels, nbaseType)
          (nop.getType, nop)

        // need to handle tuple select specially
        case TupleSelect(tup, i) =>
          val nop = TupleSelect(rec(tup)._2, i)
          (nop.getType, nop)
        case Operator(args, op) =>
          val nargs = args.map(arg => rec(arg)._2)
          val nop = op(nargs)
          (nop.getType, nop)
        case t: Terminal =>
          (t.getType, t)
      }
      //println(s"Inferred type of $e : ${res._1} new expression: ${res._2}")
      if (res._1 == Untyped) {
        throw new IllegalStateException(s"Cannot infer type for expression: $e")
      }
      res
    }

    def subcast(oldType: ClassType, newType: ClassType): Option[ClassType] = {
      newType match {
        case AbstractClassType(absClass, tps) if absClass.knownCCDescendants.contains(oldType.classDef) =>
          //here oldType.classDef <: absClass
          Some(CaseClassType(oldType.classDef.asInstanceOf[CaseClassDef], tps))
        case cct: CaseClassType =>
          Some(cct)
        case _ =>
          None
      }
    }
    rec(ine)._2
  }
}
