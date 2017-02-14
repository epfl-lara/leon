/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package phases

import purescala.Common.{ Identifier }
import purescala.Definitions.{ ClassDef, Definition, FunDef, ModuleDef, Program }
import purescala.DefOps.{ pathFromRoot }
import purescala.{ TreeTraverser }

import ExtraOps._

import collection.mutable.{ Set => MutableSet }

/*
 * Compute the dependencies of the main function and its mandatory "_main" sibling.
 *
 * The list of dependencies includes "_main" but not "main" as the later is
 * annoted with @extern (cf. ExtractEntryPointPhase).
 *
 * Moreover, the list of dependencies only contains top level functions. For nested
 * functions, we need to compute their "context" (i.e. capture free variable) to
 * hoist them. This is done in a later phase. However, if a nested function uses
 * some type T, then T (and all its class hierarchy if T is a class) will be included
 * in the dependency set.
 *
 * This phase also make sure @cCode.drop function are not used. The same is *NOT*
 * done for dropped types as they might still be present in function signature. They
 * should be removed in a later (transformation) phase. Additionally, this phase
 * ensures that the annotation set on class and function is sane.
 *
 * NOTE We cannot rely on purescala.DependencyFinder as it will traverse functions
 *     annotated with @cCode.function and we don't want that. The same applies for
 *     classes annotated with @cCode.typdef. We therefore implement a simpler version
 *     of it here based on a TreeTraverser.
 */
private[genc] object ComputeDependenciesPhase extends TimedLeonPhase[(Program, Definition), Dependencies] {
  val name = "Dependency computer"
  val description = "Compute the dependencies of a given definition"

  def getTimer(ctx: LeonContext) = ctx.timers.genc.get("compute dependencies")

  def apply(ctx: LeonContext, input: (Program, Definition)): Dependencies = {
    val (prog, entryPoint) = input

    val reporter = MiniReporter(ctx)
    import reporter._

    def isNestedFun(d: Definition): Boolean = d match {
      case fd: FunDef =>
        val parentDef = pathFromRoot(fd)(prog).reverse(1)

        parentDef match {
          case _: ModuleDef => false
          case _: FunDef => true
          case d => internalError(s"Unexpected definition ${d.id} of ${d.getClass} as parent of ${fd.id}")
        }

      case _ => false
    }

    def validateClassAnnotations(cd: ClassDef): Unit = {
      val pos = cd.getPos

      if (cd.isManuallyTyped && cd.isDropped)
        fatalError(s"${cd.id} cannot be both dropped and manually defined", pos)

      if (cd.isGeneric && cd.isManuallyTyped)
        fatalError(s"${cd.id} cannot be both a generic type and manually defined", pos)

      if (cd.isManuallyTyped && cd.hasParent)
        fatalError(s"${cd.id} cannot be manually defined because it is part of a class hierarchy", pos)

      if (cd.isRecursive)
        fatalError(s"${cd.id} and other recursive types are not supported")
      if (!cd.isManuallyTyped) {
        if (cd.isRecursive) fatalError("Recursive types are not supported", pos)
        if (cd.isCaseObject) fatalError("Case Objects are not supported", pos)
        if (cd.methods.length > 0) internalError("Methods") // They should have been lifted before
      }
    }

    def validateFunAnnotations(fd: FunDef): Unit = {
      val pos = fd.getPos

      // Those next three tests could be carried out on all functions, not just dependencies
      if (fd.isExtern && !fd.isManuallyDefined && !fd.isDropped)
        fatalError("Extern functions need to be either manually defined or dropped", pos)

      if (fd.isManuallyDefined && fd.isDropped)
        fatalError("Functions cannot be dropped and manually implemented at the same time", pos)

      if (fd.isGeneric && fd.isManuallyDefined)
        fatalError(s"Functions cannot be both a generic function and manually defined", pos)

      // This last test is specific to dependencies.
      if (fd.isDropped)
        fatalError(s"Dropped functions shall not be used", fd.getPos)
    }

    val finder = new ComputeDependenciesImpl(ctx)
    val allDeps = finder(entryPoint)

    // Ensure all annotations are sane on all dependencies, including nested functions.
    allDeps foreach {
      case fd: FunDef => validateFunAnnotations(fd)
      case cd: ClassDef => validateClassAnnotations(cd)
      case _ => ()
    }

    // Keep only the top level functions
    val deps = allDeps filterNot isNestedFun

    Dependencies(prog, deps)
  }
}

// ComputeDependenciesImpl is agnostic to what should go or not in the dependency set;
// for example, nested functions will get registered. However, it will not traverse the body
// of function definition annotated with @cCode.function nor process fields of a @cCode.typedef
// class definition.
private final class ComputeDependenciesImpl(val ctx: LeonContext) extends MiniReporter with TreeTraverser {
  private val dependencies = MutableSet[Definition]()

  // Compute the dependencies of `entry`, which includes itself.
  def apply(entry: Definition): Set[Definition] = {
    entry match {
      case e: FunDef => traverse(e)
      case _ => internalError("unexpected type of entry point: ${entry.getClass}")
    }

    dependencies.toSet
  }

  override def traverse(id: Identifier): Unit = traverse(id.getType)

  override def traverse(cd: ClassDef): Unit = if (!dependencies(cd)) {
    dependencies += cd

    if (!cd.isManuallyTyped) {
      // Visite the whole class hierarchy with their fields, recursiverly
      cd.root.knownDescendants foreach traverse
      cd.fieldsIds foreach traverse
    }
  }

  override def traverse(fd: FunDef): Unit = if (!dependencies(fd)) {
    dependencies += fd

    if (!fd.isManuallyDefined) {
      // Visite return type, body & arguments
      traverse(fd.returnType)
      traverse(fd.fullBody)
      fd.params foreach { vd => traverse(vd.id) }
    }
  }

}

