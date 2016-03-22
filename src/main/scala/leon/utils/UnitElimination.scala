/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.Extractors._
import purescala.Constructors._
import purescala.Types._

// FIXME: Unused and untested
object UnitElimination extends TransformationPhase {

  val name = "Unit Elimination"
  val description = "Remove all usage of the Unit type and value"

  private var fun2FreshFun: Map[FunDef, FunDef] = Map()
  private var id2FreshId: Map[Identifier, Identifier] = Map()

  def apply(ctx: LeonContext, pgm: Program): Program = {
    val newUnits = pgm.units map { u => u.copy(defs = u.defs.map { 
      case m: ModuleDef =>
        fun2FreshFun = Map()
        val allFuns = m.definedFunctions
        //first introduce new signatures without Unit parameters
        allFuns.foreach(fd => {
          if(fd.returnType != UnitType && fd.params.exists(vd => vd.getType == UnitType)) {
            val freshFunDef = fd.duplicate(params = fd.params.filterNot(vd => vd.getType == UnitType))
            fun2FreshFun += (fd -> freshFunDef)
          } else {
            fun2FreshFun += (fd -> fd) //this will make the next step simpler
          }
        })

        //then apply recursively to the bodies
        val newFuns = allFuns.collect{ case fd if fd.returnType != UnitType =>
          val newFd = fun2FreshFun(fd)
          newFd.fullBody = removeUnit(fd.fullBody)
          newFd
        }

        ModuleDef(m.id, m.definedClasses ++ newFuns, m.isPackageObject )
      case d =>
        d
    })}


    Program(newUnits)
  }

  private def simplifyType(tpe: TypeTree): TypeTree = tpe match {
    case TupleType(tpes) => tupleTypeWrap(tpes.map(simplifyType).filterNot{ _ == UnitType })
    case t => t
  }

  //remove unit value as soon as possible, so expr should never be equal to a unit
  private def removeUnit(expr: Expr): Expr = {
    assert(expr.getType != UnitType)
    expr match {
      case fi@FunctionInvocation(tfd, args) =>
        val newArgs = args.filterNot(arg => arg.getType == UnitType)
        FunctionInvocation(fun2FreshFun(tfd.fd).typed(tfd.tps), newArgs).setPos(fi)

      case IsTyped(Tuple(args), TupleType(tpes)) =>
        val newArgs = tpes.zip(args).collect {
          case (tp, arg) if tp != UnitType => arg
        }
        tupleWrap(newArgs.map(removeUnit)) // @mk: FIXME this may actually return a Unit, is that cool?

      case ts@TupleSelect(t, index) =>
        val TupleType(tpes) = t.getType
        val simpleTypes = tpes map simplifyType
        val newArity = tpes.count(_ != UnitType)
        val newIndex = simpleTypes.take(index).count(_ != UnitType)
        tupleSelect(removeUnit(t), newIndex, newArity)

      case Let(id, e, b) =>
        if(id.getType == UnitType)
          removeUnit(b)
        else {
          id.getType match {
            case TupleType(tpes) if tpes.contains(UnitType) => {
              val newTupleType = tupleTypeWrap(tpes.filterNot(_ == UnitType))
              val freshId = FreshIdentifier(id.name, newTupleType)
              id2FreshId += (id -> freshId)
              val newBody = removeUnit(b)
              id2FreshId -= id
              Let(freshId, removeUnit(e), newBody)
            }
            case _ => Let(id, removeUnit(e), removeUnit(b))
          }
        }

      case LetDef(fds, b) =>
        val nonUnits = fds.filter(fd => fd.returnType != UnitType)
        if(nonUnits.isEmpty) {
          removeUnit(b)
        } else {
          val fdtoFreshFd = for(fd <- nonUnits) yield {
            val m = if(fd.params.exists(vd => vd.getType == UnitType)) {
              val freshFunDef = fd.duplicate(params = fd.params.filterNot(vd => vd.getType == UnitType))
              fd -> freshFunDef
            } else {
              fd -> fd
            }
            fun2FreshFun += m
            m
          }
          for((fd, freshFunDef) <- fdtoFreshFd) {
            if(fd.params.exists(vd => vd.getType == UnitType)) {
              freshFunDef.fullBody = removeUnit(fd.fullBody)
            } else {
              fd.body = fd.body.map(b => removeUnit(b))
            }
          }
          val rest = removeUnit(b)
          val newFds = for((fd, freshFunDef) <- fdtoFreshFd) yield {
            fun2FreshFun -= fd
            if(fd.params.exists(vd => vd.getType == UnitType)) {
              freshFunDef
            } else {
              fd
            }
          }
          
          letDef(newFds, rest)
        }

      case ite@IfExpr(cond, tExpr, eExpr) =>
        val thenRec = removeUnit(tExpr)
        val elseRec = removeUnit(eExpr)
        IfExpr(removeUnit(cond), thenRec, elseRec)

      case v @ Variable(id) =>
        if(id2FreshId.isDefinedAt(id))
          Variable(id2FreshId(id))
        else v

      case m @ MatchExpr(scrut, cses) =>
        val scrutRec = removeUnit(scrut)
        val csesRec = cses.map{ cse =>
          MatchCase(cse.pattern, cse.optGuard map removeUnit, removeUnit(cse.rhs))
        }
        matchExpr(scrutRec, csesRec).setPos(m)

      case Operator(args, recons) =>
        recons(args.map(removeUnit))

      case _ => sys.error("not supported: " + expr)
    }
  }

}
