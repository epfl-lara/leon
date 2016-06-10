/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import Types._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

/** Accumulate dependency information for a program
  *
  * As long as the Program does not change, you should reuse the same
  * DependencyFinder, as it could cache its computation internally. If the program
  * does change, all bets are off.
  */
class DependencyFinder {
  private val deps: MutableMap[Definition, Set[Definition]] = MutableMap.empty

  /** Return all dependencies for a given Definition
    *
    * Use a cache internally, so two calls (from the same instance of DependencyFinder)
    * will return the same Set without re-computing. A dependency for ClassDef `d` is
    * any ClassDef references by the fields of any class in the hierarch of the `d`, as
    * well as any class invariants in the hierarchy.
    *
    * Dependencies for FunDef are any ClassDef that appear in any types (parameter list,
    * return value) as well as transitive dependencies via the body (a function invocation
    * in the body will generate a dependency to the fundef of the call).
    *
    * A def does not depend on itself by default. But if it calls itself recursively, or
    * via some transitive dependencies, then the return set will contain the input def.
    */
  def apply(d: Definition): Set[Definition] = deps.getOrElse(d, {
    new Finder(d).dependencies
  })

  private class Finder(private var current: Definition) extends TreeTraverser {
    val foundDeps: MutableMap[Definition, MutableSet[Definition]] = MutableMap.empty

    private def withCurrent[T](d: Definition)(b: => T): T = {
      if (!(foundDeps contains d)) foundDeps(d) = MutableSet.empty
      val c = current
      current = d
      val res = b
      current = c
      res
    }

    override def traverse(id: Identifier): Unit = traverse(id.getType)

    override def traverse(cd: ClassDef): Unit = if (!foundDeps(current)(cd)) {
      foundDeps(current) += cd
      if (!(deps contains cd) && !(foundDeps contains cd)) traverseClassDef(cd)
    }

    private def traverseClassDef(cd: ClassDef): Unit = {
      for (cd <- cd.root.knownDescendants :+ cd) {
        cd.invariant foreach (fd => withCurrent(cd)(traverse(fd)))
        withCurrent(cd)(cd.fieldsIds foreach traverse)
        cd.parent foreach { p =>
          foundDeps(p.classDef) = foundDeps.getOrElse(p.classDef, MutableSet.empty) + cd
          foundDeps(cd) = foundDeps.getOrElse(cd, MutableSet.empty) + p.classDef
        }
      }
    }

    override def traverse(fd: FunDef): Unit = if (!foundDeps(current)(fd)) {
      foundDeps(current) += fd
      if (!(deps contains fd) && !(foundDeps contains fd)) traverseFunDef(fd)
    }

    private def traverseFunDef(fd: FunDef): Unit = withCurrent(fd) {
      fd.params foreach (vd => traverse(vd.id))
      traverse(fd.returnType)
      traverse(fd.fullBody)
    }

    def dependencies: Set[Definition] = {
      current match {
        case fd: FunDef => traverseFunDef(fd)
        case cd: ClassDef => traverseClassDef(cd)
        case _ =>
      }

      for ((d, ds) <- foundDeps) {
        deps(d) = deps.getOrElse(d, Set.empty) ++ ds
      }

      var changed = false
      do {
        changed = false
        for ((d, ds) <- deps.toSeq) {
          val next = ds ++ ds.flatMap(d => deps.getOrElse(d, Set.empty))
          if (!(next subsetOf ds)) {
            deps(d) = next
            changed = true
          }
        }
      } while (changed)

      deps(current)
    }
  }
}
