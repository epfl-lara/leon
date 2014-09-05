/* Copyright 2009-2014 EPFL, Lausanne */

package leon
package utils

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import xlang.Trees._
import purescala.Extractors._
import purescala.TypeTrees._

object UnitElimination extends TransformationPhase {

  val name = "Unit Elimination"
  val description = "Remove all usage of the Unit type and value"

  private var fun2FreshFun: Map[FunDef, FunDef] = Map()
  private var id2FreshId: Map[Identifier, Identifier] = Map()

  def apply(ctx: LeonContext, pgm: Program): Program = {
    val newUnits = pgm.units map { u => u.copy(modules = u.modules.map { m =>
      fun2FreshFun = Map()
      val allFuns = m.definedFunctions

      //first introduce new signatures without Unit parameters
      allFuns.foreach(fd => {
        if(fd.returnType != UnitType && fd.params.exists(vd => vd.tpe == UnitType)) {
          val freshFunDef = new FunDef(FreshIdentifier(fd.id.name), fd.tparams, fd.returnType, fd.params.filterNot(vd => vd.tpe == UnitType), fd.defType).setPos(fd)
          freshFunDef.precondition = fd.precondition //TODO: maybe removing unit from the conditions as well..
          freshFunDef.postcondition = fd.postcondition//TODO: maybe removing unit from the conditions as well..
          freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
          fun2FreshFun += (fd -> freshFunDef)
        } else {
          fun2FreshFun += (fd -> fd) //this will make the next step simpler
        }
      })

      //then apply recursively to the bodies
      val newFuns = allFuns.flatMap(fd => if(fd.returnType == UnitType) Seq() else {
        val newBody = fd.body.map(body => removeUnit(body))
        val newFd = fun2FreshFun(fd)
        newFd.body = newBody
        Seq(newFd)
      })

      ModuleDef(m.id, m.definedClasses ++ newFuns, m.isStandalone )
    })}


    Program(pgm.id, newUnits)
  }

  private def simplifyType(tpe: TypeTree): TypeTree = tpe match {
    case TupleType(tpes) => tpes.map(simplifyType).filterNot{ case UnitType => true case _ => false } match {
      case Seq() => UnitType
      case Seq(tpe) => tpe
      case tpes => TupleType(tpes)
    }
    case t => t
  }

  //remove unit value as soon as possible, so expr should never be equal to a unit
  private def removeUnit(expr: Expr): Expr = {
    assert(expr.getType != UnitType)
    expr match {
      case fi@FunctionInvocation(tfd, args) => {
        val newArgs = args.filterNot(arg => arg.getType == UnitType)
        FunctionInvocation(fun2FreshFun(tfd.fd).typed(tfd.tps), newArgs).setPos(fi)
      }
      case t@Tuple(args) => {
        val TupleType(tpes) = t.getType
        val (newTpes, newArgs) = tpes.zip(args).filterNot{ case (UnitType, _) => true case _ => false }.unzip
        Tuple(newArgs.map(removeUnit)).setType(TupleType(newTpes))
      }
      case ts@TupleSelect(t, index) => {
        val TupleType(tpes) = t.getType
        val selectionType = tpes(index-1)
        val (_, newIndex) = tpes.zipWithIndex.foldLeft((0,-1)){
          case ((nbUnit, newIndex), (tpe, i)) =>
            if(i == index-1) (nbUnit, index - nbUnit) else (if(tpe == UnitType) nbUnit + 1 else nbUnit, newIndex)
        }
        TupleSelect(removeUnit(t), newIndex).setType(selectionType)
      }
      case Let(id, e, b) => {
        if(id.getType == UnitType)
          removeUnit(b)
        else {
          id.getType match {
            case TupleType(tpes) if tpes.exists(_ == UnitType) => {
              val newTupleType = TupleType(tpes.filterNot(_ == UnitType))
              val freshId = FreshIdentifier(id.name).setType(newTupleType)
              id2FreshId += (id -> freshId)
              val newBody = removeUnit(b)
              id2FreshId -= id
              Let(freshId, removeUnit(e), newBody)
            }
            case _ => Let(id, removeUnit(e), removeUnit(b))
          }
        }
      }
      case LetDef(fd, b) => {
        if(fd.returnType == UnitType) 
          removeUnit(b)
        else {
          val (newFd, rest) = if(fd.params.exists(vd => vd.tpe == UnitType)) {
            val freshFunDef = new FunDef(FreshIdentifier(fd.id.name), fd.tparams, fd.returnType, fd.params.filterNot(vd => vd.tpe == UnitType), fd.defType).setPos(fd)
            freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
            freshFunDef.precondition = fd.precondition //TODO: maybe removing unit from the conditions as well..
            freshFunDef.postcondition = fd.postcondition//TODO: maybe removing unit from the conditions as well..
            fun2FreshFun += (fd -> freshFunDef)
            freshFunDef.body = fd.body.map(b => removeUnit(b))
            val restRec = removeUnit(b)
            fun2FreshFun -= fd
            (freshFunDef, restRec)
          } else {
            fun2FreshFun += (fd -> fd)
            fd.body = fd.body.map(b => removeUnit(b))
            val restRec = removeUnit(b)
            fun2FreshFun -= fd
            (fd, restRec)
          }
          LetDef(newFd, rest)
        }
      }
      case ite@IfExpr(cond, tExpr, eExpr) => {
        val thenRec = removeUnit(tExpr)
        val elseRec = removeUnit(eExpr)
        IfExpr(removeUnit(cond), thenRec, elseRec).setType(thenRec.getType)
      }
      case n @ NAryOperator(args, recons) => {
        recons(args.map(removeUnit(_))).setType(n.getType)
      }
      case b @ BinaryOperator(a1, a2, recons) => {
        recons(removeUnit(a1), removeUnit(a2)).setType(b.getType)
      }
      case u @ UnaryOperator(a, recons) => {
        recons(removeUnit(a)).setType(u.getType)
      }
      case v @ Variable(id) => if(id2FreshId.isDefinedAt(id)) Variable(id2FreshId(id)) else v
      case (t: Terminal) => t
      case m @ MatchExpr(scrut, cses) => {
        val scrutRec = removeUnit(scrut)
        val csesRec = cses.map{
          case SimpleCase(pat, rhs) => SimpleCase(pat, removeUnit(rhs))
          case GuardedCase(pat, guard, rhs) => GuardedCase(pat, removeUnit(guard), removeUnit(rhs))
        }
        val tpe = csesRec.head.rhs.getType
        MatchExpr(scrutRec, csesRec).setType(tpe).setPos(m)
      }
      case _ => sys.error("not supported: " + expr)
    }
  }

}
