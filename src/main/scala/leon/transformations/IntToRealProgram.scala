package leon
package transformations

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import leon.purescala.ScalaPrinter

import invariant.factories._
import invariant.util.Util._
import invariant.structure._

abstract class ProgramTypeTransformer {
  protected var defmap = Map[ClassDef, ClassDef]()
  protected var idmap = Map[Identifier, Identifier]()
  protected var newFundefs = Map[FunDef, FunDef]()

  def mapField(cdef: CaseClassDef, fieldId: Identifier): Identifier = {
    (cdef.fieldsIds.collectFirst {
      case fid @ _ if (fid.name == fieldId.name) => fid
    }).get
  }

  def mapClass[T <: ClassDef](cdef: T): T = {
    if (defmap.contains(cdef)) {
      defmap(cdef).asInstanceOf[T]
    } else {
      cdef match {
        case ccdef: CaseClassDef =>
          val newparent = if (ccdef.hasParent) {
            val absType = ccdef.parent.get
            Some(AbstractClassType(mapClass(absType.classDef), absType.tps))
          } else None
          val newclassDef = ccdef.copy(id = FreshIdentifier(ccdef.id.name, ccdef.id.getType, true), parent = newparent)

          //important: register a child if a parent was newly created.
          if (newparent.isDefined)
            newparent.get.classDef.registerChild(newclassDef)

          defmap += (ccdef -> newclassDef)
          newclassDef.setFields(ccdef.fields.map(mapDecl))
          newclassDef.asInstanceOf[T]

        case acdef: AbstractClassDef =>
          val newparent = if (acdef.hasParent) {
            val absType = acdef.parent.get
            Some(AbstractClassType(mapClass(absType.classDef), absType.tps))
          } else None
          val newClassDef = acdef.copy(id = FreshIdentifier(acdef.id.name, acdef.id.getType, true), parent = newparent)
          defmap += (acdef -> newClassDef)
          newClassDef.asInstanceOf[T]
      }
    }
  }

  def mapId(id: Identifier): Identifier = {
    val newtype = mapType(id.getType)
    val newId = idmap.getOrElse(id, {
      //important need to preserve distinction between template variables and ordinary variables
      val freshId = if (TemplateIdFactory.IsTemplateIdentifier(id)) TemplateIdFactory.copyIdentifier(id)
      else FreshIdentifier(id.name, newtype, true)
      idmap += (id -> freshId)
      freshId
    })
    newId
  }

  def mapDecl(decl: ValDef): ValDef = {
    val newtpe = mapType(decl.getType)
    new ValDef(mapId(decl.id), Some(newtpe))
  }

  def mapType(tpe: TypeTree): TypeTree = {
    tpe match {
      case t @ RealType => mapNumericType(t)
      case t @ IntegerType => mapNumericType(t)
      case AbstractClassType(adef, tps) => AbstractClassType(mapClass(adef), tps)
      case CaseClassType(cdef, tps) => CaseClassType(mapClass(cdef), tps)
      case TupleType(bases) => TupleType(bases.map(mapType))
      case _ => tpe
    }
  }

  def mapNumericType(tpe: TypeTree): TypeTree

  def mapLiteral(lit: Literal[_]): Literal[_]

  def transform(program: Program): Program = {
    //create a new fundef for each function in the program
    //Unlike functions, classes are created lazily as required.
    newFundefs = program.definedFunctions.map((fd) => {
      val newFunType = FunctionType(fd.tparams.map((currParam) => currParam.tp), fd.returnType)
      val newfd = new FunDef(FreshIdentifier(fd.id.name, newFunType, true), fd.tparams,
          mapType(fd.returnType), fd.params.map(mapDecl))
      (fd, newfd)
    }).toMap

    /**
     * Here, we assume that tuple-select and case-class-select have been reduced
     */
    def transformExpr(e: Expr): Expr = e match {
      case l: Literal[_] => mapLiteral(l)
      case v @ Variable(inId) => mapId(inId).toVariable
      case FunctionInvocation(TypedFunDef(intfd, tps), args) => FunctionInvocation(TypedFunDef(newFundefs(intfd), tps), args.map(transformExpr))
      case CaseClass(CaseClassType(classDef, tps), args) => CaseClass(CaseClassType(mapClass(classDef), tps), args.map(transformExpr))
      case IsInstanceOf(expr, CaseClassType(classDef, tps)) => IsInstanceOf(transformExpr(expr), CaseClassType(mapClass(classDef), tps))
      case CaseClassSelector(CaseClassType(classDef, tps), expr, fieldId) => {
        val newtype = CaseClassType(mapClass(classDef), tps)
        CaseClassSelector(newtype, transformExpr(expr), mapField(newtype.classDef, fieldId))
      }
      //need to handle 'let' and 'letTuple' specially
      case Let(binder, value, body) => Let(mapId(binder), transformExpr(value), transformExpr(body))
      case t: Terminal => t
      /*case UnaryOperator(arg, op) => op(transformExpr(arg))
      case BinaryOperator(arg1, arg2, op) => op(transformExpr(arg1), transformExpr(arg2))*/
      case Operator(args, op) => op(args.map(transformExpr))
    }

    //create a body, pre, post for each newfundef
    newFundefs.foreach((entry) => {
      val (fd, newfd) = entry

      //add a new precondition
      newfd.precondition =
        if (fd.precondition.isDefined)
          Some(transformExpr(fd.precondition.get))
        else None

      //add a new body
      newfd.body = if (fd.hasBody) {
        //replace variables by constants if possible
        val simpBody = matchToIfThenElse(fd.body.get)
        Some(transformExpr(simpBody))
      } else Some(NoTree(fd.returnType))

      // FIXME
      //add a new postcondition
      newfd.fullBody = if (fd.postcondition.isDefined && newfd.body.isDefined) {
        val Lambda(Seq(ValDef(resid, _)), pexpr) = fd.postcondition.get
        val tempRes = mapId(resid).toVariable
        Ensuring(newfd.body.get, Lambda(Seq(ValDef(tempRes.id, Some(tempRes.getType))), transformExpr(pexpr)))
        // Some(mapId(resid), transformExpr(pexpr))
      } else NoTree(fd.returnType)

      fd.flags.foreach(newfd.addFlag(_))
    })

    val newprog = copyProgram(program, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => newFundefs(fd)
      case cd: ClassDef => mapClass(cd)
      case d @ _ => throw new IllegalStateException("Unknown Definition: " + d)
    })
    newprog
  }
}

class IntToRealProgram extends ProgramTypeTransformer {

  private var realToIntId = Map[Identifier, Identifier]()

  def mapNumericType(tpe: TypeTree) = {
    require(isNumericType(tpe))
    tpe match {
      case IntegerType => RealType
      case _ => tpe
    }
  }

  def mapLiteral(lit: Literal[_]): Literal[_] = lit match {
    case IntLiteral(v) => FractionalLiteral(v, 1)
    case _ => lit
  }

  def apply(program: Program): Program = {

    val newprog = transform(program)
    //reverse the map
    realToIntId = idmap.map(entry => (entry._2 -> entry._1))
    //println("After Real Program Conversion: \n" + ScalaPrinter.apply(newprog))
    //print all the templates
    /*newprog.definedFunctions.foreach((fd) => {
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      if (funinfo.isDefined && funinfo.get.hasTemplate)
        println("Function: " + fd.id + " template --> " + funinfo.get.getTemplate)
    })*/
    newprog
  }

  /**
   * Assuming that the model maps only variables
   */
  def unmapModel(model: Map[Identifier, Expr]): Map[Identifier, Expr] = {
    model.map((pair) => {
      val (key, value) = if (realToIntId.contains(pair._1)) {
        (realToIntId(pair._1), pair._2)
      } else pair
      (key -> value)
    })
  }
}

class RealToIntProgram extends ProgramTypeTransformer {
  val debugIntToReal = false
  val bone = BigInt(1)

  def mapNumericType(tpe: TypeTree) = {
    require(isNumericType(tpe))
    tpe match {
      case RealType => IntegerType
      case _ => tpe
    }
  }

  def mapLiteral(lit: Literal[_]): Literal[_] = lit match {
    case FractionalLiteral(v, `bone`) => InfiniteIntegerLiteral(v)
    case FractionalLiteral(_, _) => throw new IllegalStateException("Cannot convert real to integer: " + lit)
    case _ => lit
  }

  def apply(program: Program): Program = {

    val newprog = transform(program)

    if (debugIntToReal)
      println("Program to Verify: \n" + ScalaPrinter.apply(newprog))

    newprog
  }

  def mappedFun(fd: FunDef): FunDef = newFundefs(fd)
}