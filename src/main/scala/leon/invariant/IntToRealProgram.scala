package leon
package invariant

import purescala.ScalaPrinter
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import leon.LeonContext
import leon.LeonPhase
import leon.invariant._

abstract class ProgramTypeTransformer {
  protected var defmap = Map[ClassTypeDef, ClassTypeDef]()  
  protected var idmap = Map[Identifier, Identifier]()  
  protected var newFundefs = Map[FunDef, FunDef]()

  def mapField(cdef : CaseClassDef, fieldId : Identifier) : Identifier = {
    (cdef.fieldsIds.collectFirst {
      case fid@_ if (fid.name == fieldId.name) => fid
    }).get
  } 
  
  def mapClass[T <: ClassTypeDef](cdef: T): T = {
    if (defmap.contains(cdef)) {
      defmap(cdef).asInstanceOf[T]
    } else {
      cdef match {
        case ccdef: CaseClassDef =>          
          val newclassDef = new CaseClassDef(FreshIdentifier(ccdef.id.name,true))
          defmap += (ccdef -> newclassDef)
          newclassDef.fields = ccdef.fields.map(mapDecl)
          if (ccdef.hasParent) {
            newclassDef.setParent(mapClass(ccdef.parent.get))
          }
          newclassDef.asInstanceOf[T]

        case acdef: AbstractClassDef =>
          val newClassDef = new AbstractClassDef(FreshIdentifier(acdef.id.name,true))
          defmap += (acdef -> newClassDef)
          if (acdef.hasParent) {
            newClassDef.setParent(mapClass(acdef.parent.get))
          }
          newClassDef.asInstanceOf[T]
      }
    }
  }
  
  def mapId(id: Identifier): Identifier = {
      val newtype = mapType(id.getType)
      val newId = idmap.getOrElse(id, {
        //important need to preserve distinction between template variables and ordinary variables
        val freshId = if (TemplateIdFactory.IsTemplateIdentifier(id)) TemplateIdFactory.copyIdentifier(id)
        else FreshIdentifier(id.name, true).setType(newtype)
        idmap += (id -> freshId)
        freshId
      })
      newId
    }
  
  def mapDecl(decl: VarDecl): VarDecl = {
    val newtpe = mapType(decl.tpe)
    new VarDecl(mapId(decl.id), newtpe)
  }

  def mapType(tpe: TypeTree): TypeTree = {
    tpe match {
      case t : NumericType => mapNumericType(t)
      case AbstractClassType(adef) => AbstractClassType(mapClass(adef))
      case CaseClassType(cdef) => CaseClassType(mapClass(cdef))
      case TupleType(bases) => TupleType(bases.map(mapType))
      case _ => tpe
    }
  }   
  
  def mapNumericType(tpe: TypeTree with NumericType) : TypeTree with NumericType
  
  def mapLiteral(lit: Literal[_]) : Literal[_] 
  
  def transform(program: Program): Program = {
    //create a new fundef for each function in the program
    //Unlike functions, classes are created lazily as required.     
    newFundefs = program.mainObject.definedFunctions.map((fd) => {
      val newfd = new FunDef(FreshIdentifier(fd.id.name,true), mapType(fd.returnType), fd.args.map(mapDecl))
      (fd, newfd)
    }).toMap    

    /**
     * Here, we assume that tuple-select and case-class-select have been reduced
     */
    def transformExpr(e: Expr): Expr = e match {
      case l : Literal[_] => mapLiteral(l)      
      case v @ Variable(inId) => mapId(inId).toVariable      
      case FunctionInvocation(intfd, args) => FunctionInvocation(newFundefs(intfd), args.map(transformExpr))
      case CaseClass(classDef, args) => CaseClass(mapClass(classDef), args.map(transformExpr))
      case CaseClassInstanceOf(classDef, expr) => CaseClassInstanceOf(mapClass(classDef), transformExpr(expr))
      case CaseClassSelector(classDef, expr, fieldId) => {
        val newclass = mapClass(classDef)
        CaseClassSelector(newclass, transformExpr(expr), mapField(newclass,fieldId))
      }
      //need to handle 'let' and 'letTuple' specially
      case Let(binder, value, body) => Let(mapId(binder), transformExpr(value), transformExpr(body))
      case LetTuple(binders, value, body) => LetTuple(binders.map(mapId), transformExpr(value), transformExpr(body))
      case t: Terminal => t
      case UnaryOperator(arg, op) => op(transformExpr(arg))
      case BinaryOperator(arg1, arg2, op) => op(transformExpr(arg1), transformExpr(arg2))
      case NAryOperator(args, op) => op(args.map(transformExpr))
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
      } else None

      //add a new postcondition                        
      newfd.postcondition = if (fd.postcondition.isDefined) {
        val (resid, pexpr) = fd.postcondition.get               
        Some(mapId(resid), transformExpr(pexpr))
      } else None

      //important: update function info of 'newfd'       
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      if (funinfo.isDefined) {
        FunctionInfoFactory.createFunctionInfo(newfd, transformExpr, funinfo.get)
      }

      fd.annotations.foreach((str) => newfd.addAnnotation(str))
    })
    val newDefs = program.mainObject.defs.map {
      case fd: FunDef => newFundefs(fd)
      case cd: ClassTypeDef => mapClass(cd)
      case d@_ => throw IllegalStateException("Unknown Definition: "+d)
    }
    val newprog = program.copy(mainObject = program.mainObject.copy(defs = newDefs))    
    newprog
  }
}

class IntToRealProgram extends ProgramTypeTransformer {

  private var realToIntId = Map[Identifier, Identifier]()

  def mapNumericType(tpe: TypeTree with NumericType) = {
    tpe match {
      case Int32Type => RealType      
      case _ => tpe
    }
  }

  def mapLiteral(lit: Literal[_]) : Literal[_] = lit match {
    case IntLiteral(v) => RealLiteral(v,1)
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

  def mapNumericType(tpe: TypeTree with NumericType) = {
    tpe match {
      case RealType => Int32Type      
      case _ => tpe
    }
  }
  
  def mapLiteral(lit: Literal[_]) : Literal[_] = lit match {
    case RealLiteral(v,1) => IntLiteral(v)
    case RealLiteral(_,_) => throw IllegalStateException("Cannot convert real to integer: "+lit)
    case _ => lit
  }

  def apply(program: Program): Program = {
    
    val newprog = transform(program)
    //println("Program to Verify: \n" + ScalaPrinter.apply(newprog))
    //print all the templates
    /*newprog.definedFunctions.foreach((fd) => {
      val funinfo = FunctionInfoFactory.getFunctionInfo(fd)
      if (funinfo.isDefined && funinfo.get.hasTemplate)
        println("Function: " + fd.id + " template --> " + funinfo.get.getTemplate)
    })*/
    newprog
  }  
  
  def mappedFun(fd: FunDef) : FunDef = newFundefs(fd)
}