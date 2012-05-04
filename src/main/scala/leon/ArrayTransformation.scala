package leon

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TypeTrees._

object ArrayTransformation extends Pass {

  val description = "Add bound checking for array access and remove side effect array update operations"

  def apply(pgm: Program): Program = {

    fd2fd = Map()
    id2id = Map()

    val allFuns = pgm.definedFunctions

    val newFuns: Seq[FunDef] = allFuns.map(fd => {
      if(fd.hasImplementation) {
        val args = fd.args
        if(args.exists(vd => containsArrayType(vd.tpe)) || containsArrayType(fd.returnType)) {
          val newArgs = args.map(vd => {
            val freshId = FreshIdentifier(vd.id.name).setType(TupleType(Seq(vd.tpe, Int32Type)))
            id2id += (vd.id -> freshId)
            val newTpe = transform(vd.tpe)
            VarDecl(freshId, newTpe)
          })
          val freshFunName = FreshIdentifier(fd.id.name)
          val freshFunDef = new FunDef(freshFunName, transform(fd.returnType), newArgs)
          freshFunDef.fromLoop = fd.fromLoop
          freshFunDef.parent = fd.parent
          freshFunDef.precondition = fd.precondition.map(transform)
          freshFunDef.postcondition = fd.postcondition.map(transform)
          freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
          fd2fd += (fd -> freshFunDef)
          freshFunDef
        } else fd
      } else fd
    })

    allFuns.zip(newFuns).foreach{ case (ofd, nfd) => ofd.body.map(body => {
      val newBody = transform(body)
      nfd.body = Some(newBody)
    })}

    val Program(id, ObjectDef(objId, _, invariants)) = pgm
    val allClasses: Seq[Definition] = pgm.definedClasses
    Program(id, ObjectDef(objId, allClasses ++ newFuns, invariants))
  }


  private def transform(tpe: TypeTree): TypeTree = tpe match {
    case ArrayType(base) => TupleType(Seq(ArrayType(transform(base)), Int32Type))
    case TupleType(tpes) => TupleType(tpes.map(transform))
    case t => t
  }
  private def containsArrayType(tpe: TypeTree): Boolean = tpe match {
    case ArrayType(base) => true
    case TupleType(tpes) => tpes.exists(containsArrayType)
    case t => false
  }

  private var id2id: Map[Identifier, Identifier] = Map()
  private var fd2fd: Map[FunDef, FunDef] = Map()

  private def transform(expr: Expr): Expr = expr match {
    case fill@ArrayFill(length, default) => {
      var rLength = transform(length)
      val rDefault = transform(default)
      val rFill = ArrayMake(rDefault).setType(fill.getType)
      Tuple(Seq(rFill, rLength)).setType(TupleType(Seq(fill.getType, Int32Type)))
    }
    case sel@ArraySelect(a, i) => {
      val ar = transform(a)
      val ir = transform(i)
      val length = TupleSelect(ar, 2).setType(Int32Type)
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        ArraySelect(TupleSelect(ar, 1), ir).setType(sel.getType).setPosInfo(sel),
        Error("Index out of bound").setType(sel.getType).setPosInfo(sel)
      ).setType(sel.getType)
    }
    case up@ArrayUpdate(a, i, v) => {
      val ar = transform(a)
      val ir = transform(i)
      val vr = transform(v)
      val Variable(id) = ar
      val length = TupleSelect(ar, 2).setType(Int32Type)
      val array = TupleSelect(ar, 1).setType(ArrayType(v.getType))
      //val Tuple(Seq(Variable(id), length)) = ar
      IfExpr(
        And(GreaterEquals(i, IntLiteral(0)), LessThan(i, length)),
        Block(Seq(
          Assignment(
            id, 
            Tuple(Seq(
              ArrayUpdated(array, i, v).setType(array.getType).setPosInfo(up),
              length)
            ).setType(TupleType(Seq(array.getType, Int32Type))))),
          IntLiteral(0)),
        Error("Index out of bound").setType(Int32Type).setPosInfo(up)
      ).setType(Int32Type)
    }
    case ArrayLength(a) => {
      val ar = transform(a)
      TupleSelect(ar, 2).setType(Int32Type)
    }
    case Let(i, v, b) => {
      val vr = transform(v)
      v.getType match {
        case ArrayType(_) => {
          val freshIdentifier = FreshIdentifier("t").setType(vr.getType)
          id2id += (i -> freshIdentifier)
          val br = transform(b)
          LetVar(freshIdentifier, vr, br)
        }
        case _ => {
          val br = transform(b)
          Let(i, vr, br)
        }
      }
    }
    case LetVar(id, e, b) => {
      val er = transform(e)
      val br = transform(b)
      LetVar(id, er, br)
    }
    case wh@While(c, e) => {
      val newWh = While(transform(c), transform(e))
      newWh.invariant = wh.invariant.map(i => transform(i))
      newWh.setPosInfo(wh)
    }

    case ite@IfExpr(c, t, e) => {
      val rc = transform(c)
      val rt = transform(t)
      val re = transform(e)
      IfExpr(rc, rt, re).setType(rt.getType)
    }

    case m @ MatchExpr(scrut, cses) => {
      val scrutRec = transform(scrut)
      val csesRec = cses.map{
        case SimpleCase(pat, rhs) => SimpleCase(pat, transform(rhs))
        case GuardedCase(pat, guard, rhs) => GuardedCase(pat, transform(guard), transform(rhs))
      }
      val tpe = csesRec.head.rhs.getType
      MatchExpr(scrutRec, csesRec).setType(tpe).setPosInfo(m)
    }
    case LetDef(fd, b) => {
      val newFd = if(fd.hasImplementation) {
        val body = fd.body.get
        val args = fd.args
        val newFd = 
          if(args.exists(vd => containsArrayType(vd.tpe)) || containsArrayType(fd.returnType)) {
            val newArgs = args.map(vd => {
              val freshId = FreshIdentifier(vd.id.name).setType(TupleType(Seq(vd.tpe, Int32Type)))
              id2id += (vd.id -> freshId)
              val newTpe = transform(vd.tpe)
              VarDecl(freshId, newTpe)
            })
            val freshFunName = FreshIdentifier(fd.id.name)
            val freshFunDef = new FunDef(freshFunName, transform(fd.returnType), newArgs)
            freshFunDef.fromLoop = fd.fromLoop
            freshFunDef.parent = fd.parent
            freshFunDef.precondition = fd.precondition.map(transform)
            freshFunDef.postcondition = fd.postcondition.map(transform)
            freshFunDef.addAnnotation(fd.annotations.toSeq:_*)
            fd2fd += (fd -> freshFunDef)
            freshFunDef
          } else fd
        val newBody = transform(body)
        newFd.body = Some(newBody)
        newFd
      } else fd
      val rb = transform(b)
      LetDef(newFd, rb)
    }
    case FunctionInvocation(fd, args) => {
      val rargs = args.map(transform)
      val rfd = fd2fd.get(fd).getOrElse(fd)
      FunctionInvocation(rfd, rargs)
    }

    case n @ NAryOperator(args, recons) => recons(args.map(transform)).setType(n.getType)
    case b @ BinaryOperator(a1, a2, recons) => recons(transform(a1), transform(a2)).setType(b.getType)
    case u @ UnaryOperator(a, recons) => recons(transform(a)).setType(u.getType)

    case v @ Variable(id) => if(id2id.isDefinedAt(id)) Variable(id2id(id)) else v
    case (t: Terminal) => t
    case unhandled => scala.sys.error("Non-terminal case should be handled in ArrayTransformation: " + unhandled)

  }

}
