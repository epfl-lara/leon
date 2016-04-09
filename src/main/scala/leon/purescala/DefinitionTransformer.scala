/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Extractors._
import Types._

import utils._
import scala.collection.mutable.{Map => MutableMap}

class DefinitionTransformer(
  idMap: Bijection[Identifier, Identifier] = new Bijection[Identifier, Identifier],
  fdMap: Bijection[FunDef    , FunDef    ] = new Bijection[FunDef    , FunDef    ],
  cdMap: Bijection[ClassDef  , ClassDef  ] = new Bijection[ClassDef  , ClassDef  ]) extends TreeTransformer {

  private def transform(id: Identifier, freshen: Boolean): Identifier = {
    val ntpe = transform(id.getType)
    if (ntpe == id.getType && !freshen) id else id.duplicate(tpe = ntpe)
  }

  override def transform(id: Identifier): Identifier = idMap.cachedB(id) {
    transform(id, false)
  }

  protected def transformFunDef(fd: FunDef): Option[FunDef] = None
  override def transform(fd: FunDef): FunDef = {
    if ((fdMap containsB fd) || (tmpFdMap containsB fd)) fd
    else if (tmpFdMap containsA fd) tmpFdMap.toB(fd)
    else fdMap.getBorElse(fd, {
      transformDefs(fd)
      fdMap.toB(fd)
    })
  }

  protected def transformClassDef(cd: ClassDef): Option[ClassDef] = None
  override def transform(cd: ClassDef): ClassDef = {
    if ((cdMap containsB cd) || (tmpCdMap containsB cd)) cd
    else if (tmpCdMap containsA cd) tmpCdMap.toB(cd)
    else cdMap.getBorElse(cd, {
      transformDefs(cd)
      cdMap.toB(cd)
    })
  }

  private val dependencies = new DependencyFinder
  private val tmpCdMap = new Bijection[ClassDef, ClassDef]
  private val tmpFdMap = new Bijection[FunDef  , FunDef  ]

  private def transformDefs(base: Definition): Unit = {
    val deps = dependencies(base) + base
    val (cds, fds) = {
      val (c, f) = deps.partition(_.isInstanceOf[ClassDef])
      (c.map(_.asInstanceOf[ClassDef]), f.map(_.asInstanceOf[FunDef]))
    }

    for (cd <- cds if !(cdMap containsA cd) && !(cdMap containsB cd))
      tmpCdMap += cd -> transformClassDef(cd).getOrElse(cd)

    for (fd <- fds if !(fdMap containsA fd) && !(fdMap containsB fd))
      tmpFdMap += fd -> transformFunDef(fd).getOrElse(fd)

    val requireCache: MutableMap[Definition, Boolean] = MutableMap.empty
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

    tmpCdMap.clear()
    tmpFdMap.clear()

    val nonReq = deps filterNot allReq
    cdMap ++= nonReq collect { case cd: ClassDef => cd -> cd }
    fdMap ++= nonReq collect { case fd: FunDef => fd -> fd }

    def trCd(cd: ClassDef): ClassDef = cdMap.cachedB(cd) {
      val parent = cd.parent.map(act => act.copy(classDef = trCd(act.classDef).asInstanceOf[AbstractClassDef]))
      cd match {
        case acd: AbstractClassDef => acd.duplicate(id = transform(acd.id, true), parent = parent)
        case ccd: CaseClassDef => ccd.duplicate(id = transform(ccd.id, true), parent = parent)
      }
    }

    for (cd <- requiredCds) trCd(cd)
    for (fd <- requiredFds) {
      val newId = transform(fd.id, true)
      val newReturn = transform(fd.returnType)
      val newParams = fd.params map (vd => ValDef(transform(vd.id)))
      fdMap += fd -> fd.duplicate(id = newId, params = newParams, returnType = newReturn)
    }

    for (ccd <- requiredCds collect { case ccd: CaseClassDef => ccd }) {
      val newCcd = cdMap.toB(ccd).asInstanceOf[CaseClassDef]
      newCcd.setFields(ccd.fields.map(vd => ValDef(transform(vd.id))))
      ccd.invariant.foreach(fd => newCcd.setInvariant(transform(fd)))
    }

    for (fd <- requiredFds) {
      val nfd = fdMap.toB(fd)
      val bindings = (fd.params zip nfd.params).map(p => p._1.id -> p._2.id).toMap ++
        nfd.params.map(vd => vd.id -> vd.id)

      nfd.fullBody = transform(nfd.fullBody)(bindings)
    }
  }
}

