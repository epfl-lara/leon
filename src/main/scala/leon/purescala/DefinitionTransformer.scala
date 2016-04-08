/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import Types._

import utils._
import scala.collection.mutable.{Set => MutableSet}

class DefinitionTransformer(
  idMap: Bijection[Identifier, Identifier] = new Bijection[Identifier, Identifier],
  fdMap: Bijection[FunDef    , FunDef    ] = new Bijection[FunDef    , FunDef    ],
  cdMap: Bijection[ClassDef  , ClassDef  ] = new Bijection[ClassDef  , ClassDef  ]) extends TreeTransformer {

  override def transform(id: Identifier): Identifier = idMap.cachedB(id) {
    val ntpe = transform(id.getType)
    if (ntpe == id.getType) id else id.duplicate(tpe = ntpe)
  }

  override def transform(fd: FunDef): FunDef = fdMap.getBorElse(fd, if (tmpDefs(fd)) fd else {
    transformDefs(fd)
    fdMap.toB(fd)
  })

  override def transform(cd: ClassDef): ClassDef = cdMap.getBorElse(cd, if (tmpDefs(cd)) cd else {
    transformDefs(cd)
    cdMap.toB(cd)
  })

  private val dependencies = new DependencyFinder
  private val tmpDefs: MutableSet[Definition] = MutableSet.empty

  private def transformDefs(base: Definition): Unit = {
    val deps = dependencies(base) + base
    val (cds, fds) = {
      val (c, f) = deps.partition(_.isInstanceOf[ClassDef])
      (c.map(_.asInstanceOf[ClassDef]), f.map(_.asInstanceOf[FunDef]))
    }

    tmpDefs ++= cds.filterNot(cdMap containsA _) ++ fds.filterNot(fdMap containsA _)

    var requireCache: Map[Definition, Boolean] = Map.empty
    def required(d: Definition): Boolean = requireCache.getOrElse(d, {
      val res = d match {
        case fd: FunDef =>
          val newReturn = transform(fd.returnType)
          lazy val newParams = fd.params.map(vd => ValDef(transform(vd.id)))
          lazy val newBody = transform(fd.fullBody)((fd.params.map(_.id) zip newParams.map(_.id)).toMap)
          newReturn != fd.returnType || newParams != fd.params || newBody != fd.fullBody

        case cd: ClassDef =>
          cd.fieldsIds.exists(id => transform(id.getType) != id.getType) ||
          cd.invariant.exists(required)

        case _ => scala.sys.error("Should never happen!?")
      }

      requireCache += d -> res
      res
    })

    val req = deps filter required
    val allReq = req ++ (deps filter (d => (dependencies(d) & req).nonEmpty))
    val requiredCds = allReq collect { case cd: ClassDef => cd }
    val requiredFds = allReq collect { case fd: FunDef => fd }
    tmpDefs --= deps

    val nonReq = deps filterNot allReq
    cdMap ++= nonReq collect { case cd: ClassDef => cd -> cd }
    fdMap ++= nonReq collect { case fd: FunDef => fd -> fd }

    def trCd(cd: ClassDef): ClassDef = cdMap.cachedB(cd) {
      val parent = cd.parent.map(act => act.copy(classDef = trCd(act.classDef).asInstanceOf[AbstractClassDef]))
      cd match {
        case acd: AbstractClassDef => acd.duplicate(id = transform(acd.id), parent = parent)
        case ccd: CaseClassDef => ccd.duplicate(id = transform(ccd.id), parent = parent)
      }
    }

    for (cd <- requiredCds) trCd(cd)
    for (fd <- requiredFds) {
      val newReturn = transform(fd.returnType)
      val newParams = fd.params map (vd => ValDef(transform(vd.id)))
      fdMap += fd -> fd.duplicate(id = transform(fd.id), params = newParams, returnType = newReturn)
    }

    for (ccd <- requiredCds collect { case ccd: CaseClassDef => ccd }) {
      val newCcd = cdMap.toB(ccd).asInstanceOf[CaseClassDef]
      newCcd.setFields(ccd.fields.map(vd => ValDef(transform(vd.id))))
      ccd.invariant.foreach(fd => newCcd.setInvariant(transform(fd)))
    }

    for (fd <- requiredFds) {
      val nfd = fdMap.toB(fd)
      nfd.fullBody = transform(fd.fullBody)((fd.params zip nfd.params).map(p => p._1.id -> p._2.id).toMap)
    }
  }
}

