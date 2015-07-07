/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import ExprOps._
import Types._
import Constructors.and
import TypeOps.instantiateType
import Constructors.application

object MethodLifting extends TransformationPhase {

  val name = "Method Lifting"
  val description = "Translate methods into functions of the companion object"

  // Takes cd and its subclasses and creates cases that together will form a composite method.
  // fdId is the method id which will be searched for in the subclasses.
  // cd is the hierarchy root
  // A Seq of MatchCases is returned, along with a boolean that signifies if the matching is complete.
  private def makeCases(cd: ClassDef, fdId: Identifier, breakDown: Expr => Expr): (Seq[MatchCase], Boolean) = cd match {
    case ccd: CaseClassDef =>
      ccd.methods.find( _.id == fdId) match {
        case None =>
          (List(), false)
        case Some(m) =>
          val ct = ccd.typed
          val binder = FreshIdentifier(ccd.id.name.toLowerCase, ct, true)
          val fBinders = ct.fields.map{ f => f.id -> f.id.freshen }.toMap
          def subst(e: Expr): Expr = e match {
            case CaseClassSelector(`ct`, This(`ct`), i) =>
              Variable(fBinders(i)).setPos(e)
            case This(`ct`) =>
              Variable(binder).setPos(e)
            case e =>
              e
          }
          val newE = simplePreTransform(subst)(breakDown(m.fullBody))
          val subPatts = ct.fields map (f => WildcardPattern(Some(fBinders(f.id))))
          val cse = SimpleCase(CaseClassPattern(Some(binder), ct, subPatts), newE).setPos(newE)
          (List(cse), true)
      }
    case acd: AbstractClassDef =>
      val (r, c) = acd.knownChildren.map(makeCases(_, fdId, breakDown)).unzip
      val recs = r.flatten
      val complete = !(c contains false)
      if (complete) {
        // Children define all cases completely, we don't need to add anything
        (recs, true)
      } else if (!acd.methods.exists( m => m.id == fdId && m.body.nonEmpty)) {
        // We don't have anything to add
        (recs, false)
      } else {
        // We have something to add
        val m = acd.methods.find( m => m.id == fdId ).get
        val at = acd.typed
        val binder = FreshIdentifier(acd.id.name.toLowerCase, at, true)
        def subst(e: Expr): Expr = e match {
          case This(`at`) =>
            Variable(binder)
          case e =>
            e
        }
        val newE = simplePreTransform(subst)(breakDown(m.fullBody))
        val cse = SimpleCase(InstanceOfPattern(Some(binder), at), newE).setPos(newE)
        (recs :+ cse, true)
      }

  }


  def apply(ctx: LeonContext, program: Program): Program = {

    // First we create the appropriate functions from methods:
    var mdToFds = Map[FunDef, FunDef]()

    val newUnits = for (u <- program.units) yield {
      var fdsOf = Map[String, Set[FunDef]]()

      // Lift methods to the root class
      for {
        c <- u.definedClassesOrdered
        if c.parent.isDefined
        fd <- c.methods
        if c.ancestors.forall(!_.methods.map{_.id}.contains(fd.id))
      } {
        val root = c.ancestors.last
        val tMap = c.tparams.zip(root.tparams.map{_.tp}).toMap
        val tSubst: TypeTree => TypeTree  = instantiateType(_, tMap)

        val fdParams = fd.params map { vd =>
          val newId = FreshIdentifier(vd.id.name, tSubst(vd.id.getType))
          ValDef(newId).setPos(vd.getPos)
        }
        val paramsMap = fd.params.zip(fdParams).map{ case (from, to) => from.id -> to.id }.toMap
        val eSubst: Expr => Expr = instantiateType(_, tMap, paramsMap)

        val newFd = new FunDef(fd.id, fd.tparams, tSubst(fd.returnType), fdParams).copiedFrom(fd)
        newFd.copyContentFrom(fd)
        val prec = fd.precondition.getOrElse(BooleanLiteral(true))
        newFd.fullBody = eSubst(withPrecondition(
          newFd.fullBody,
          Some(and(
            prec,
            IsInstanceOf(
              c.typed(root.tparams.map{ _.tp }),
              This(root.typed)
            )
          ))
        ))

        c.unregisterMethod(fd.id)
        root.registerMethod(newFd)
      }

      // 1) Create one function for each method
      for { cd <- u.classHierarchyRoots if cd.methods.nonEmpty; fd <- cd.methods } {
        // We import class type params and freshen them
        val ctParams = cd.tparams map { _.freshen }
        val tparamsMap = cd.tparams.zip(ctParams map { _.tp }).toMap

        val id = fd.id.freshen
        val recType = cd.typed(ctParams.map(_.tp))
        val retType = instantiateType(fd.returnType, tparamsMap)
        val fdParams = fd.params map { vd =>
          val newId = FreshIdentifier(vd.id.name, instantiateType(vd.id.getType, tparamsMap))
          ValDef(newId).setPos(vd.getPos)
        }

        val receiver = FreshIdentifier("thiss", recType).setPos(cd.id)

        val nfd = new FunDef(id, ctParams ++ fd.tparams, retType, ValDef(receiver) +: fdParams)
        nfd.copyContentFrom(fd)
        nfd.setPos(fd)
        nfd.addFlag(IsMethod(cd))

        if (cd.knownDescendents.forall( _.methods.forall(_.id != fd.id))) {
          val paramsMap = fd.params.zip(fdParams).map{case (x,y) => (x.id, y.id)}.toMap
          // Don't need to compose methods
          nfd.fullBody = postMap {
            case th@This(ct) if ct.classDef == cd =>
              Some(receiver.toVariable.setPos(th))
            case _ =>
              None
          }(instantiateType(nfd.fullBody, tparamsMap, paramsMap))
        } else {
          // We need to compose methods of subclasses

          /* (Type) parameter substitutions that look at all subclasses */
          val paramsMap = (for {
            c <- cd.knownDescendents :+ cd
            m <- c.methods if m.id == fd.id
            (from,to) <- m.params zip fdParams
          } yield (from.id, to.id)).toMap
          val classParamsMap = (for {
            c <- cd.knownDescendents :+ cd
            (from, to) <- c.tparams zip ctParams
          } yield (from, to.tp)).toMap
          val methodParamsMap = (for {
            c <- cd.knownDescendents :+ cd
            m <- c.methods if m.id == fd.id
            (from,to) <- m.tparams zip fd.tparams
          } yield (from, to.tp)).toMap
          def inst(cs: Seq[MatchCase]) = instantiateType(
            MatchExpr(Variable(receiver), cs).setPos(fd),
            classParamsMap ++ methodParamsMap,
            paramsMap
          )

          /* Separately handle pre, post, body */
          val (pre, _)  = makeCases(cd, fd.id, preconditionOf(_).getOrElse(BooleanLiteral(true)))
          val (post, _) = makeCases(cd, fd.id, postconditionOf(_).getOrElse(
            Lambda(Seq(ValDef(FreshIdentifier("res", retType, true))), BooleanLiteral(true))
          ))
          val (body, _) = makeCases(cd, fd.id, withoutSpec(_).getOrElse(NoTree(retType)))

          /* Some obvious simplifications */
          val preSimple = {
            val trivial = pre.forall { _.rhs == BooleanLiteral(true) }
            if (trivial) None else Some(inst(pre).setPos(fd.getPos))
          }
          val postSimple = {
            val trivial = post.forall {
              case SimpleCase(_, Lambda(_, BooleanLiteral(true))) => true
              case _ => false
            }
            if (trivial) None
            else {
              val resVal = FreshIdentifier("res", retType, true)
              Some(Lambda(
                Seq(ValDef(resVal)),
                inst(post map { cs => cs.copy( rhs =
                  application(cs.rhs, Seq(Variable(resVal)))
                )})
              ).setPos(fd))
            }
          }
          val bodySimple = {
            val trivial = body forall {
              case SimpleCase(_, NoTree(_)) => true
              case _ => false
            }
            if (trivial) NoTree(retType) else inst(body)
          }

          /* Construct full body */
          nfd.fullBody = withPostcondition(
            withPrecondition(bodySimple, preSimple),
            postSimple
          )

        }
        mdToFds += fd -> nfd
        fdsOf += cd.id.name -> (fdsOf.getOrElse(cd.id.name, Set()) + nfd)
      }

      // 2) Place functions in existing companions:
      val defs = u.defs map {
        case md: ModuleDef if fdsOf contains md.id.name =>
          val fds = fdsOf(md.id.name)
          fdsOf -= md.id.name
          ModuleDef(md.id, md.defs ++ fds, false)
        case d => d
      }

      // 3) Create missing companions
      val newCompanions = for ((name, fds) <- fdsOf) yield {
        ModuleDef(FreshIdentifier(name), fds.toSeq, false)
      }

      u.copy(defs = defs ++ newCompanions)
    }

    val pgm = Program(newUnits)

    // 4) Remove methods in classes
    for (cd <- pgm.definedClasses) {
      cd.clearMethods()
    }

    // 5) Replace method calls with function calls
    for (fd <- pgm.definedFunctions) {
      fd.fullBody = postMap{
        case mi @ MethodInvocation(IsTyped(rec, ct: ClassType), cd, tfd, args) =>
          Some(FunctionInvocation(mdToFds(tfd.fd).typed(ct.tps ++ tfd.tps), rec +: args).setPos(mi))
        case _ => None
      }(fd.fullBody)
    }

    pgm
  }

}
