package leon
package invariant.transformations
import purescala.Common._
import purescala.Definitions._
import purescala.Extractors._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import invariant._

import invariant.engine._
import invariant.factories._
import invariant.util._
import invariant.structure._

abstract class ProgramTypeTransformer {
  protected var defmap = Map[ClassDef, ClassDef]()  
  protected var idmap = Map[Identifier, Identifier]()  
  protected var newFundefs = Map[FunDef, FunDef]()

  def mapField(cdef : CaseClassDef, fieldId : Identifier) : Identifier = {
    (cdef.fieldsIds.collectFirst {
      case fid@_ if (fid.name == fieldId.name) => fid
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
          val newclassDef = ccdef.copy(id = FreshIdentifier(ccdef.id.name, true), parent = newparent)
          
          //important: register a child if a parent was newly created.
          if(newparent.isDefined)
        	  newparent.get.classDef.registerChildren(newclassDef)
            
          defmap += (ccdef -> newclassDef)
          newclassDef.setFields(ccdef.fields.map(mapDecl))
          newclassDef.asInstanceOf[T]

        case acdef: AbstractClassDef =>
          val newparent = if (acdef.hasParent) {
            val absType = acdef.parent.get
            Some(AbstractClassType(mapClass(absType.classDef), absType.tps))
          } else None
          val newClassDef = acdef.copy(id = FreshIdentifier(acdef.id.name, true), parent = newparent)
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
        else FreshIdentifier(id.name, true).setType(newtype)
        idmap += (id -> freshId)
        freshId
      })
      newId
    }
  
  def mapDecl(decl: ValDef): ValDef = {
    val newtpe = mapType(decl.tpe)
    new ValDef(mapId(decl.id), newtpe)
  }

  def mapType(tpe: TypeTree): TypeTree = {
    tpe match {
      case t : NumericType => mapNumericType(t)
      case AbstractClassType(adef, tps) => AbstractClassType(mapClass(adef), tps)
      case CaseClassType(cdef, tps) => CaseClassType(mapClass(cdef), tps)
      case TupleType(bases) => TupleType(bases.map(mapType))
      case _ => tpe
    }
  }   
  
  def mapNumericType(tpe: TypeTree with NumericType) : TypeTree with NumericType
  
  def mapLiteral(lit: Literal[_]) : Literal[_] 
  
  def transform(program: Program): Program = {
    //create a new fundef for each function in the program
    //Unlike functions, classes are created lazily as required.     
    newFundefs = program.definedFunctions.map((fd) => {
      val newfd = new FunDef(FreshIdentifier(fd.id.name,true), fd.tparams, mapType(fd.returnType), fd.params.map(mapDecl))
      (fd, newfd)
    }).toMap    

    /**
     * Here, we assume that tuple-select and case-class-select have been reduced
     */
    def transformExpr(e: Expr): Expr = e match {
      case l : Literal[_] => mapLiteral(l)      
      case v @ Variable(inId) => mapId(inId).toVariable      
      case FunctionInvocation(TypedFunDef(intfd, tps), args) => FunctionInvocation(TypedFunDef(newFundefs(intfd), tps), args.map(transformExpr))
      case CaseClass(CaseClassType(classDef, tps), args) => CaseClass(CaseClassType(mapClass(classDef), tps), args.map(transformExpr))
      case CaseClassInstanceOf(CaseClassType(classDef, tps), expr) => CaseClassInstanceOf(CaseClassType(mapClass(classDef),tps), transformExpr(expr))
      case CaseClassSelector(CaseClassType(classDef,tps), expr, fieldId) => {
        val newtype = CaseClassType(mapClass(classDef), tps)
        CaseClassSelector(newtype, transformExpr(expr), mapField(newtype.classDef,fieldId))
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
    
    val newprog = Util.copyProgram(program, (defs: Seq[Definition]) => defs.map {
      case fd: FunDef => newFundefs(fd)
      case cd: ClassDef => mapClass(cd)
      case d@_ => throw IllegalStateException("Unknown Definition: "+d)
    })    
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