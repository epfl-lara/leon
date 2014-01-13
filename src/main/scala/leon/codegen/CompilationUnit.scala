/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package codegen

import purescala.Common._
import purescala.Definitions._
import purescala.Trees._
import purescala.TreeOps._
import purescala.TypeTrees._
import purescala.TypeTreeOps._

import cafebabe._
import cafebabe.AbstractByteCodes._
import cafebabe.ByteCodes._
import cafebabe.ClassFileTypes._
import cafebabe.Flags._

import scala.collection.JavaConverters._

import java.lang.reflect.Constructor

class CompilationUnit(val ctx: LeonContext,
                      val program: Program,
                      val params: CodeGenParams = CodeGenParams()) extends CodeGeneration {

  private var _nextAnonId = 0
  protected[codegen] def nextAnonId = {
    _nextAnonId += 1
    _nextAnonId
  }

  private var _nextExprId = 0
  private def nextExprId = {
    _nextExprId += 1
    _nextExprId
  }

  val loader = new CafebabeClassLoader(classOf[CompilationUnit].getClassLoader)

  private[codegen] var defToClass : Map[Definition, ClassFile] = Map.empty
  private[codegen] var classToDef : Map[String, Definition]    = Map.empty

  def defineClass(df: Definition) {
    val cName = defToJVMName(df)

    val cf = df match {
      case ccd: CaseClassDef =>
        val pName = ccd.parent.map(parent => defToJVMName(parent.classDef))
        new ClassFile(cName, pName)

      case acd: AbstractClassDef =>
        new ClassFile(cName, None)

      case ob: ObjectDef =>
        new ClassFile(cName, None)

      case _ =>
        sys.error("Unhandled definition type")
    }

    defToClass += df -> cf
    classToDef += cf.className -> df
  }

  def jvmClassToLeonClass(name: String): Option[Definition] = classToDef.get(name)

  def leonClassToJVMClass(cd: Definition): Option[String] = defToClass.get(cd).map(_.className)

  private var defToCons  : Map[Definition, String] = Map.empty

  def leonClassToJVMInfo(cd: Definition): Option[String] = defToCons.get(cd).orElse {
    cd match {
      case ccd : CaseClassDef =>
        val sig = "(" + ccd.fields.map(f => typeToJVM(f.tpe)).mkString("") + ")V"
        defToCons += ccd -> sig
        Some(sig)
      case _ => None
    }
  }

  // Returns className, methodName, methodSignature
  private[this] var funDefInfo = Map[FunDef, (String, String, String)]()

  def leonFunDefToJVMInfo(fd: FunDef): Option[(String, String, String)] = {
    funDefInfo.get(fd).orElse {
      val monitorType = if (params.requireMonitor) "L"+MonitorClass+";" else ""

      val sig = "(" + monitorType + fd.args.map(a => typeToJVM(a.tpe)).mkString("") + ")" + typeToJVM(fd.returnType)

      leonClassToJVMClass(program.mainObject) match {
        case Some(cn) =>
          val res = (cn, fd.id.uniqueName, sig)
          funDefInfo += fd -> res
          Some(res)
        case None =>
          None
      }
    }
  }

  // Get the Java constructor corresponding to the Case class
  private[this] var ccdConstructors = Map[CaseClassDef, Constructor[_]]()

  private[this] def caseClassConstructor(ccd: CaseClassDef): Option[Constructor[_]] = {
    ccdConstructors.get(ccd).orElse {
      defToClass.get(ccd) match {
        case Some(cf) =>
          val klass = loader.loadClass(cf.className)
          // This is a hack: we pick the constructor with the most arguments.
          val conss = klass.getConstructors().sortBy(_.getParameterTypes().length)
          assert(!conss.isEmpty)
          val cons = conss.last

          ccdConstructors += ccd -> cons
          Some(cons)
        case None =>
          None
      }
    }
  }

  private[this] lazy val tupleConstructor: Constructor[_] = {
    val tc = loader.loadClass("leon.codegen.runtime.Tuple")
    val conss = tc.getConstructors().sortBy(_.getParameterTypes().length)
    assert(!conss.isEmpty)
    conss.last
  }

  private[this] lazy val arrayConstructor: Constructor[_] = {
    val ac = loader.loadClass("leon.codegen.runtime.Array")
    val conss = ac.getConstructors().sortBy(_.getParameterTypes().length)
    assert(!conss.isEmpty)
    conss.last
  }

  // Currently, this method is only used to prepare arguments to reflective calls.
  // This means it is safe to return AnyRef (as opposed to primitive types), because
  // reflection needs this anyway.
  private[codegen] def exprToJVM(e: Expr): AnyRef = e match {
    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case Tuple(elems) =>
      tupleConstructor.newInstance(elems.map(exprToJVM).toArray).asInstanceOf[AnyRef]

    case FiniteArray(elems) =>
      arrayConstructor.newInstance(elems.map(exprToJVM).toArray).asInstanceOf[AnyRef]

    case CaseClass(cct, args) =>
      caseClassConstructor(cct.classDef) match {
        case Some(cons) =>
          cons.newInstance(args.map(exprToJVM).toArray : _*).asInstanceOf[AnyRef]
        case None =>
          ctx.reporter.fatalError("Case class constructor not found?!?")
      }

    /*
    // For now, we only treat boolean arrays separately.
    // We have a use for these, mind you.
    case f @ FiniteArray(exprs) if f.getType == ArrayType(BooleanType) =>
      exprs.map(e => valueToJVM(e).asInstanceOf[java.lang.Boolean].booleanValue).toArray
    */

    // Just slightly overkill...
    case _ =>
      compileExpression(e, Seq()).evalToJVM(Seq())
  }

  // Note that this may produce untyped expressions! (typically: sets, maps)
  private[codegen] def jvmToExpr(e: AnyRef, tpe: TypeTree): Expr = (e, tpe) match {
    case (i: Integer, Int32Type) =>
      IntLiteral(i.toInt)

    case (b: java.lang.Boolean, BooleanType) =>
      BooleanLiteral(b.booleanValue)

    case (cc: runtime.CaseClass, ct : ClassType) =>
      val fields = cc.productElements()

      jvmClassToLeonClass(e.getClass.getName) match {
        case Some(jccd: CaseClassDef) =>
          val cct : CaseClassType = ct match {
            case cct : CaseClassType =>
              assert(cct.classDef == jccd, "Unsupported classDef : " + jccd)
              cct
            case act : AbstractClassType =>
              act.knownDescendents.collect { case (cct : CaseClassType) => cct }.find(cct => cct.classDef == jccd).getOrElse {
                throw CompilationException("Unsupported classDef : " + jccd)
              }
          }
          CaseClass(cct, (fields.toList zip cct.fields).map(p => jvmToExpr(p._1, p._2.tpe)))
        case _ =>
          throw CompilationException("Unsupported return value : " + e)
      }

    case (tpl: runtime.Tuple, TupleType(argTypes)) =>
      val elems = for (i <- 0 until tpl.getArity) yield {
        jvmToExpr(tpl.get(i), argTypes(i))
      }
      Tuple(elems)

    case (arr: runtime.Array, ArrayType(base)) =>
      val elems = for (i <- 0 until arr.getLength) yield {
        jvmToExpr(arr.get(i), base)
      }
      val leonArray = FiniteArray(elems)
      leastUpperBound(elems.map(_.getType) :+ base).foreach { leonArray.setType _ }
      leonArray

    case (set : runtime.Set, SetType(base)) =>
      val leonSet = FiniteSet(set.getElements().asScala.map(jvmToExpr(_, base)).toSeq)
      leastUpperBound(leonSet.getType, SetType(base)).foreach { leonSet.setType _ }
      leonSet

    case (map : runtime.Map, MapType(from, to)) =>
      val pairs = map.getElements().asScala.map { entry =>
        val k = jvmToExpr(entry.getKey(), from)
        val v = jvmToExpr(entry.getValue(), to)
        (k, v)
      }
      val leonMap = FiniteMap(pairs.toSeq)
      leastUpperBound(leonMap.getType, MapType(from, to)).foreach { leonMap.setType _ }
      leonMap

    case _ =>
      throw CompilationException("Unsupported return value : " + e.getClass)
  }
  
  def compileExpression(e: Expr, args: Seq[Identifier]): CompiledExpression = {
    if(e.getType == Untyped) {
      throw new IllegalArgumentException("Cannot compile untyped expression [%s].".format(e))
    }

    val id = nextExprId

    val cName = "Leon$CodeGen$Expr$"+id

    val cf = new ClassFile(cName, None)
    cf.setFlags((
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    cf.addDefaultConstructor

    val argsTypes = args.map(a => typeToJVM(a.getType))

    val realArgs = if (params.requireMonitor) {
      ("L" + MonitorClass + ";") +: argsTypes
    } else {
      argsTypes
    }

    val m = cf.addMethod(
      typeToJVM(e.getType),
      "eval",
      realArgs : _*
    )

    m.setFlags((
      METHOD_ACC_PUBLIC |
      METHOD_ACC_FINAL |
      METHOD_ACC_STATIC
    ).asInstanceOf[U2])

    val ch = m.codeHandler

    val newMapping = if (params.requireMonitor) {
        args.zipWithIndex.toMap.mapValues(_ + 1)
      } else {
        args.zipWithIndex.toMap
      }

    val exprToCompile = purescala.TreeOps.matchToIfThenElse(e)

    mkExpr(exprToCompile, ch)(Locals(newMapping, Map.empty, Map.empty))

    exprToCompile.getType match {
      case Int32Type | BooleanType =>
        ch << IRETURN

      case UnitType | _: TupleType  | _: SetType | _: MapType | _: AbstractClassType | _: CaseClassType | _: ArrayType =>
        ch << ARETURN

      case other =>
        throw CompilationException("Unsupported return type : " + other)
    }

    ch.freeze

    loader.register(cf)

    new CompiledExpression(this, cf, exprToCompile, args)
  }

  def compileMainObject() {
    val cf = defToClass(program.mainObject)

    cf.addDefaultConstructor

    cf.setFlags((
      CLASS_ACC_SUPER |
      CLASS_ACC_PUBLIC |
      CLASS_ACC_FINAL
    ).asInstanceOf[U2])

    // This assumes that all functions of a given program get compiled
    // as methods of a single class file.
    for(funDef <- program.definedFunctions;
        (_,mn,_) <- leonFunDefToJVMInfo(funDef)) {
      compileFunDef(funDef, mn, cf)
    }
  }

  def init() {
    // First define all classes
    for ((parent, children) <- program.algebraicDataTypes) {
      defineClass(parent)

      for (c <- children) {
        defineClass(c)
      }
    }

    for(single <- program.singleCaseClasses) {
      defineClass(single)
    }

    defineClass(program.mainObject)
  }

  def compile() {
    // Compile everything
    for ((parent, children) <- program.algebraicDataTypes) {
      compileAbstractClassDef(parent)

      for (c <- children) {
        compileCaseClassDef(c)
      }
    }

    for(single <- program.singleCaseClasses) {
      compileCaseClassDef(single)
    }

    compileMainObject()

    defToClass.values.foreach(loader.register _)
  }

  def writeClassFiles() {
    for ((d, cl) <- defToClass) {
      cl.writeToFile(cl.className + ".class")
    }
  }

  init()
  compile()
}
