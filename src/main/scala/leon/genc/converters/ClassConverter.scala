/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package genc
package converters

import purescala.Definitions._
// NOTE don't import CAST._ to decrease possible confusion between the two ASTs

import ExtraOps._

private[converters] trait ClassConverter {
  this: Converters with MiniReporter =>

  // Register a hierarchy of class.
  //
  // - Find the top abstract class
  // - List all concreate classes
  // - Create a C enum with a value for each concreate class
  // - Create a C struct for each child
  // - Create a C struct with a union member having an entry for each concreate class
  // - Register the enum, union & the structs
  // - Return the struct representing this class hierarchy
  private def registerClassHierarchy(cd: ClassDef): CAST.Type = {
    val top = cd.getTopParent
    val id = convertToId(top.id)

    getType(id) getOrElse {
      val children = top.knownCCDescendants

      debug(s"Registrering class hierarchy of ${cd.id}")
      debug(s"Top = ${top.id}")
      debug(s"Children = ${ children map { _.id } mkString ", " }")

      val name = id.name
      val enumId = CAST.Id(s"tag_${name}_t")
      val enumValues = children map { c => CAST.Id("tag_" + convertToId(c.id).name) }
      val enumType = CAST.Enum(enumId, enumValues)

      val childrenStructs = children map registerClass
      val unionType = CAST.Union(CAST.Id(s"union_$name"), childrenStructs)

      val tag = CAST.Var(CAST.Id("tag"), enumType)
      val union = CAST.Var(CAST.Id("value"), unionType)

      val typ = CAST.Struct(CAST.Id(name), tag :: union :: Nil)

      registerEnum(enumType)
      registerType(unionType)
      registerType(typ)

      typ
    }
  }

  // Register a given class (if needed) after converting its data structure to a C one.
  // NOTE it is okay to call this function more than once on the same class definition.
  private def registerClass(cd: ClassDef): CAST.Type = {
    implicit val ctx = FunCtx.empty

    val id = convertToId(cd.id)

    val typ = getType(id)
    typ foreach { t => debug(s"$t is already defined") }

    typ getOrElse {
      val fields = cd.fields map convertToVar
      val typ = CAST.Struct(id, fields)

      registerType(typ)
      typ
    }
  }

  // Convert a given class into a C structure; make some additional checks to
  // restrict the input class to the supported set of features.
  def convertClass(cd: ClassDef): CAST.Type = {
    debug(s"Processing ${cd.id} with annotations: ${cd.annotations}")

    implicit val pos = cd.getPos

    if (cd.isManuallyTyped && cd.isDropped)
      CAST.unsupported(s"${cd.id} cannot be both dropped and manually defined")

    if (cd.isDropped) {
      debug(s"${cd.id} is dropped")
      CAST.NoType
    } else getTypedef(cd) getOrElse {
      if (cd.isCaseObject)       CAST.unsupported("Case Objects")
      if (cd.tparams.length > 0) CAST.unsupported("Type Parameters")
      if (cd.methods.length > 0) CAST.unsupported("Methods") // TODO is it?

      // Handle inheritance
      if (cd.isAbstract || cd.hasParent) registerClassHierarchy(cd)
      else registerClass(cd)
    }
  }

}

