/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package evaluators

import leon.codegen.runtime.RuntimeResources

import purescala.Definitions._
import purescala.DefOps._
import purescala.Expressions._
import purescala.Types._

import java.io.File
import java.net.URLClassLoader
import java.lang.reflect.Constructor

/**
 * Call scalac-compiled functions from within Leon
 *
 * Known limitations:
 *  - Multiple argument lists
 */
class ScalacEvaluator(ev: DeterministicEvaluator, ctx: LeonContext, pgm: Program) extends LeonComponent {
  implicit val _: Program = pgm

  val name = "Evaluator of external functions"
  val description = "Evaluator for non-purescala functions"

  implicit val debugSection = utils.DebugSectionEvaluation

  val classPaths: List[File] = ctx.classDir.toList

  lazy val runtimeTok = {
    RuntimeResources.register(this)
  }

  private def unsupported(err: String): Nothing = {
    throw new RuntimeException(err)
  }

  private def encodeName(name: String): String = {
    scala.reflect.NameTransformer.encode(name)
  }

  private def jvmName(d: Definition): String = {
    compiledName(d).replace(".", "/")
  }

  private def jvmClassName(tpe: TypeTree): String = tpe match {
    case IntegerType =>
      "scala/math/BigInt"

    case TupleType(subs) =>
      f"scala/Tuple${subs.size}%d"

    case UnitType =>
      "scala/runtime/BoxedUnit"

    case ct: ClassType =>
      jvmName(ct.classDef)

    case _ =>
      ctx.reporter.internalError(s"$tpe is not a jvm class type ?!?")
  }

  private def compiledName(d: Definition): String = {
    // Scala encodes fullname of modules using ".". After the module, it
    // becomes an inner class, with '$'
    val path = pathFromRoot(d)

    val pathToModule = path.takeWhile{!_.isInstanceOf[ModuleDef]}
    val rest = path.drop(pathToModule.size)

    val upToModule = pathToNames(pathToModule, false).map(encodeName).mkString(".")

    if(rest.isEmpty) {
      upToModule
    } else {
      d match {
        case md: ModuleDef =>
          upToModule+"."+encodeName(md.id.name)+"$"
        case _ =>
          val afterModule = pathToNames(rest, false).map(encodeName).mkString("$")
          upToModule+"."+afterModule
      }
    }
  }

  def call(tfd: TypedFunDef, args: Seq[Expr]): Expr = {
    val fd = tfd.fd

    val methodName = encodeName(fd.id.name)
    
    val jvmArgs = args.map(leonToScalac)

    val (clazz, jvmRec, jvmCallArgs) = fd.methodOwner match {
      case Some(cd) =>
        (cd, jvmArgs.head, jvmArgs.tail)

      case None =>
        val md = moduleOf(fd).get

        val jvmModule = loadClass(compiledName(md))
        val rec       = jvmModule.getField("MODULE$").get(null)

        (md, rec, jvmArgs)
    }

    val jvmClassName = compiledName(clazz)
    val jvmClass     = loadClass(jvmClassName)

    ctx.reporter.debug(s"Calling $jvmClassName.${tfd.signature}(${args.mkString(", ")})")

    // Lookup method in jvmClass

    jvmClass.getMethods().filter(_.getName() == methodName).toList match {
      case List(meth) =>

        val res = if (jvmCallArgs.isEmpty) {
          meth.invoke(jvmRec)
        } else {
          meth.invoke(jvmRec,  jvmCallArgs: _*)
        }

        scalacToLeon(res, tfd.returnType)

      case Nil =>
        unsupported(s"Unable to lookup method")

      case ms =>
        unsupported(s"Ambiguous reference to method: ${ms.size} methods found with a matching name")

    }
  }

  val localClassLoader = {
    classOf[ScalacEvaluator].getClassLoader()
  }

  val toInstrument = {
    val fds = (for (fd <- pgm.definedFunctions if !fd.annotations("extern")) yield {
      encodeName(fd.id.name) -> fd
    }).toMap

    fds.groupBy { case (n, fd) =>
      compiledName(fd.methodOwner.getOrElse(moduleOf(fd).get))
    }
  }

  val compiledClassLoader = {
    val classUrls = ctx.classDir.map(_.toURI.toURL)
    val cl = new URLClassLoader(classUrls.toArray, localClassLoader)
    new InterceptingClassLoader(cl)
  }

  def loadClass(classname: String): Class[_] = {
    compiledClassLoader.loadClass(classname)
  }

  def leonToScalac(e: Expr): AnyRef = e match {
    case CharLiteral(v) =>
      new java.lang.Character(v)

    case IntLiteral(v) =>
      new java.lang.Integer(v)

    case InfiniteIntegerLiteral(v) =>
      v

    case BooleanLiteral(v) =>
      new java.lang.Boolean(v)

    case Tuple(exprs) =>
      val name = f"scala.Tuple${exprs.size}%d"

      val cl = localClassLoader.loadClass(name)
      val constr = cl.getConstructors().head.asInstanceOf[Constructor[AnyRef]]

      constr.newInstance(exprs.map(leonToScalac) : _*)

    case UnitLiteral() =>
      Unit.box(())

    case FiniteSet(exprs, tpe) =>

      val cl = compiledClassLoader.loadClass("leon.lang.Set")
      val constr = cl.getConstructors().head.asInstanceOf[Constructor[AnyRef]]

      constr.newInstance(Set(exprs.toSeq.map(leonToScalac) : _*))

    case FiniteMap(pairs, ktpe, vtpe) =>

      val cl = compiledClassLoader.loadClass("leon.lang.Map")
      val constr = cl.getConstructors().head.asInstanceOf[Constructor[AnyRef]]

      constr.newInstance(Map(
        pairs.map { case (k, v) =>
          leonToScalac(k) -> leonToScalac(v)
        }.toSeq : _*
      ))

    case CaseClass(cct, fields) =>

      val name   = compiledName(cct.classDef)

      val cl = loadClass(name)
      val constr = cl.getConstructors().head.asInstanceOf[Constructor[AnyRef]]
      constr.newInstance(fields.map(leonToScalac) : _*)


    case Lambda(_, _) =>
      unsupported("It is not yet possible to pass a closure to an @extern function")

    case t: Terminal =>
      unsupported("Unhandled conversion to scala runtime: "+t)

    case _ =>
      unsupported("Trying to convert non-terminal: "+e)
  }

  def productToElems(p: Product, tps: Seq[TypeTree]): Seq[Expr] = {
    for ((t,i) <- tps.zipWithIndex) yield {
      scalacToLeon(p.productElement(i), t)
    }
  }

  def scalacToLeon(o: Any, t: TypeTree): Expr = t match {
    case BooleanType =>
      BooleanLiteral(o.asInstanceOf[Boolean].booleanValue)
    case Int32Type =>
      IntLiteral(o.asInstanceOf[Integer].intValue)
    case CharType =>
      CharLiteral(o.asInstanceOf[Character].charValue)
    case IntegerType =>
      InfiniteIntegerLiteral(o.asInstanceOf[BigInt])
    case UnitType =>
      UnitLiteral()
    case TupleType(tps) =>
      Tuple(productToElems(o.asInstanceOf[Product], tps))
    case cct: CaseClassType =>
      CaseClass(cct, productToElems(o.asInstanceOf[Product], cct.fieldsTypes))

    case act: AbstractClassType =>
      val className = o.getClass.getName

      act.knownCCDescendants.find(cct => compiledName(cct.classDef) == className) match {
        case Some(cct) =>
          scalacToLeon(o, cct)

        case None =>
          unsupported("Expected "+act+", got: "+className)
      }

    case SetType(b) =>
      val cl = compiledClassLoader.loadClass("leon.lang.Set")

      val s = cl.getMethod("theSet").invoke(o).asInstanceOf[Set[_]]

      FiniteSet(s.iterator.map(scalacToLeon(_, b)).toSet, b)

    case MapType(ktpe, vtpe) =>

      val cl = compiledClassLoader.loadClass("leon.lang.Map")

      val s = cl.getMethod("theMap").invoke(o).asInstanceOf[Map[_, _]]

      FiniteMap(s.iterator.map {
        case (k, v) => scalacToLeon(k, ktpe) -> scalacToLeon(v, vtpe)
      }.toMap, ktpe, vtpe)

    case FunctionType(_, _) =>
      unsupported("It is not possible to pass a closure from @extern back to leon")

    case _ =>
      unsupported("Unhandled conversion from scala runtime: "+t)
  }

  def jvmCallBack(cName: String, fName: String, args: Array[AnyRef]): AnyRef = {
    toInstrument.get(cName).flatMap(_.get(fName)) match {
      case Some(fd) =>
        val leonArgs = fd.params.map(_.getType).zip(args).map {
          case (tpe, arg) => scalacToLeon(arg, tpe)
        }

        val fi = FunctionInvocation(fd.typed, leonArgs)
        leonToScalac(ev.eval(fi).result.getOrElse {
          unsupported("Evaluation in Leon failed!")
        })

      case None =>
        unsupported("Unable to locate callback function "+cName+"."+fName)
    }
  }

  /**
   * Black magic here we come!
   */
  import org.objectweb.asm.ClassReader
  import org.objectweb.asm.ClassWriter
  import org.objectweb.asm.ClassVisitor
  import org.objectweb.asm.MethodVisitor
  import org.objectweb.asm.Opcodes

  class InterceptingClassLoader(p: ClassLoader) extends ClassLoader(p) {
    import java.io._

    var loaded = Set[String]()

    override def loadClass(name: String, resolve: Boolean): Class[_] = {
      if (loaded(name)) {
        super.loadClass(name, resolve)
      } else {
        loaded += name

        if (!(toInstrument contains name)) {
          super.loadClass(name, resolve)
        } else {
          val bs = new ByteArrayOutputStream()
          val is = getResourceAsStream(name.replace('.', '/') + ".class")
          val buf = new Array[Byte](512)
          var len = is.read(buf)
          while (len  > 0) {
            bs.write(buf, 0, len)
            len = is.read(buf)
          }

          // Transform bytecode
          val cr = new ClassReader(bs.toByteArray())
          val cw = new ClassWriter(cr, ClassWriter.COMPUTE_FRAMES)
          val cv = new LeonCallsClassVisitor(cw, name, toInstrument(name))
          cr.accept(cv, 0)

          val res = cw.toByteArray()

          defineClass(name, res, 0, res.length)
        }
      }
    }
  }

  class LeonCallsClassVisitor(cv: ClassVisitor, cName: String, fdMap: Map[String, FunDef]) extends ClassVisitor(Opcodes.ASM5, cv) {
    override def visitMethod(access: Int, fName: String, desc: String, sig: String, exceptions: Array[String]) = {
      val mv = super.visitMethod(access, fName, desc, sig, exceptions)
      if ((fdMap contains fName)) {
        new LeonCallsMethodVisitor(mv, cName, fName, fdMap(fName))
      } else {
        mv
      }
    }
  }

  class LeonCallsMethodVisitor(mv: MethodVisitor, cName: String, fName: String, fd: FunDef) extends MethodVisitor(Opcodes.ASM5, mv) {

    def box(tpe: TypeTree) = tpe match {
      case Int32Type =>
        mv.visitTypeInsn(Opcodes.NEW, "java/lang/Integer")
        mv.visitInsn(Opcodes.DUP_X1)
        mv.visitInsn(Opcodes.SWAP)
        mv.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/Integer", "<init>", "(I)V", false)

      case CharType =>
        mv.visitTypeInsn(Opcodes.NEW, "java/lang/Character")
        mv.visitInsn(Opcodes.DUP_X1)
        mv.visitInsn(Opcodes.SWAP)
        mv.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/Character", "<init>", "(C)V", false)

      case BooleanType  =>
        mv.visitTypeInsn(Opcodes.NEW, "java/lang/Boolean")
        mv.visitInsn(Opcodes.DUP_X1)
        mv.visitInsn(Opcodes.SWAP)
        mv.visitMethodInsn(Opcodes.INVOKESPECIAL, "java/lang/Boolean", "<init>", "(Z)V", false)

      case _ =>
    }

    def unbox(tpe: TypeTree) = tpe match {
      case Int32Type =>
        mv.visitTypeInsn(Opcodes.CHECKCAST, "java/lang/Integer")
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/Integer", "intValue", "()I", false)

      case CharType =>
        mv.visitTypeInsn(Opcodes.CHECKCAST, "java/lang/Character")
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/Character", "charValue", "()C", false)

      case BooleanType  =>
        mv.visitTypeInsn(Opcodes.CHECKCAST, "java/lang/Boolean")
        mv.visitMethodInsn(Opcodes.INVOKEVIRTUAL, "java/lang/Boolean", "booleanValue", "()Z", false)

      case tpe =>
        mv.visitTypeInsn(Opcodes.CHECKCAST, jvmClassName(tpe))
    }

    def loadOpCode(tpe: TypeTree) = tpe match {
      case CharType => Opcodes.ILOAD
      case Int32Type => Opcodes.ILOAD
      case BooleanType => Opcodes.ILOAD
      case _ => Opcodes.ALOAD
    }

    def returnOpCode(tpe: TypeTree) = tpe match {
      case CharType => Opcodes.IRETURN
      case Int32Type => Opcodes.IRETURN
      case BooleanType => Opcodes.IRETURN
      case UnitType => Opcodes.RETURN
      case _ => Opcodes.ARETURN
    }


    override def visitCode() {
      mv.visitLdcInsn(runtimeTok.id)
      mv.visitLdcInsn(cName)
      mv.visitLdcInsn(fName)

      // If we are visiting a method, we need to add the receiver in the arguments array
      val readOffset = fd.methodOwner match {
        case Some(cd) =>
          // $this is the receiver
          0
        case _ =>
          // We skip the module object
          1
      }

      // Array of arguments called
      mv.visitLdcInsn(fd.params.size)
      mv.visitTypeInsn(Opcodes.ANEWARRAY, "java/lang/Object")

      // Note: fd.params includes the receiver!
      // Add actual arguments, box necessary values
      for ((tpe, i) <- fd.params.map(_.getType).zipWithIndex) {
        // Array ref
        mv.visitInsn(Opcodes.DUP)
        mv.visitLdcInsn(i)
        // Arg Value
        mv.visitVarInsn(loadOpCode(tpe), i+readOffset)
        box(tpe)
        mv.visitInsn(Opcodes.AASTORE)
      }


      mv.visitMethodInsn(Opcodes.INVOKESTATIC,
                         "leon/evaluators/LeonJVMCallBacks",
                         "callBack",
                         "(ILjava/lang/String;Ljava/lang/String;[Ljava/lang/Object;)Ljava/lang/Object;",
                          false)

      unbox(fd.returnType)
      mv.visitInsn(returnOpCode(fd.returnType))
      mv.visitEnd()
    }
  }
}

object LeonJVMCallBacks {
  def callBack(token: Int, className: String, methodName: String, args: Array[AnyRef]): AnyRef = {
    val ev = RuntimeResources.get[ScalacEvaluator](token)
    ev.jvmCallBack(className, methodName, args)
  }
}
