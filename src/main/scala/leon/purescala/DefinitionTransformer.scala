/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package purescala

import Common._
import Definitions._
import Expressions._
import Types._

import utils._
import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

class DefinitionTransformer(
  idMap: Bijection[Identifier, Identifier] = new Bijection[Identifier, Identifier],
  fdMap: Bijection[FunDef    , FunDef    ] = new Bijection[FunDef    , FunDef    ],
  cdMap: Bijection[ClassDef  , ClassDef  ] = new Bijection[ClassDef  , ClassDef  ]) extends TreeTransformer {

  private def transformId(id: Identifier, freshen: Boolean): Identifier = {
    val ntpe = transform(id.getType)
    if (ntpe == id.getType && !freshen) id else id.duplicate(tpe = ntpe)
  }

  def transformType(tpe: TypeTree): Option[TypeTree] = None
  final override def transform(tpe: TypeTree): TypeTree = {
    super.transform(transformType(tpe).getOrElse(tpe))
  }

  final override def transform(id: Identifier): Identifier = {
    val ntpe = transform(id.getType)
    idMap.getB(id) match {
      case Some(nid) if ntpe == nid.getType => nid
      case _ =>
        val nid = transformId(id, false)
        idMap += id -> nid
        nid
    }
  }

  def transformExpr(e: Expr)(implicit bindings: Map[Identifier, Identifier]): Option[Expr] = None
  final override def transform(e: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = {
    transformExpr(e) match {
      case Some(r) => super.transform(r)
      case None    => super.transform(e)
    }
  }

  protected def transformFunDef(fd: FunDef): Option[FunDef] = None
  final override def transform(fd: FunDef): FunDef = {
    if ((fdMap containsB fd) || (tmpFdMap containsB fd)) fd
    else if (tmpFdMap containsA fd) tmpFdMap.toB(fd)
    else fdMap.getBorElse(fd, {
      transformDefs(fd)
      fdMap.toB(fd)
    })
  }

  def inverse = {
    def inverse[T](bi1: Bijection[T, T]): Bijection[T, T] = {
      val bi2 = new Bijection[T, T]();

      for ((a, b) <- bi1) {
        bi2 += b -> a;
      }

      bi2
    }
    new DefinitionTransformer(inverse(idMap), inverse(fdMap), inverse(cdMap))
  }


  /** Override this to provide specific ClassDef transform
    *
    * It is guaranteed to only be called once per ClassDef accross the whole
    * program transformation, and won't be applied recursively
    * to the transformed class.
    *
    * This design choice is to allow for a typical use case in which you
    * want to add a field to every single case classes in your program,
    * and for obvious reasons you don't want to apply this transformation
    * recursively on transformed case classes. Another typical case is
    * to duplicate the whole program, which needs duplicating each case
    * class by freshening all the fields. Without this specific contract,
    * client implementation of such functionalities would require the use
    * of a local map to track which classes are in the program before starting
    * the transformation, and which classes was already transformed.
    */
  protected def transformClassDef(cd: ClassDef): Option[ClassDef] = None
  final override def transform(cd: ClassDef): ClassDef = {
    if ((cdMap containsB cd) || (tmpCdMap containsB cd)) cd
    else if (tmpCdMap containsA cd) tmpCdMap.toB(cd)
    else
      cdMap.getBorElse(cd, {
      transformDefs(cd)
      cdMap.toB(cd)
    })
  }

  private val dependencies = new DependencyFinder
  private val tmpCdMap = new Bijection[ClassDef, ClassDef]
  private val tmpFdMap = new Bijection[FunDef  , FunDef  ]
  private val fieldsSet: MutableSet[CaseClassDef] = MutableSet.empty[CaseClassDef]

  private def transformDefs(base: Definition): Unit = {
    val (cds, fds) = {
      val deps = dependencies(base) + base
      val (c, f) = deps.partition(_.isInstanceOf[ClassDef])
      val cds = c.map(_.asInstanceOf[ClassDef]).filter(cd => !(cdMap containsA cd) && !(cdMap containsB cd))
      val fds = f.map(_.asInstanceOf[FunDef]).filter(fd => !(fdMap containsA fd) && !(fdMap containsB fd))
      (cds, fds)
    }

    val transformedCds = (for (cd <- cds if !(cdMap containsA cd) && !(cdMap containsB cd)) yield {
      val ncd = transformClassDef(cd).getOrElse(cd)
      tmpCdMap += cd -> ncd
      if (cd ne ncd) Some(cd -> ncd) else None
    }).flatten.toMap

    val transformedFds = (for (fd <- fds if !(fdMap containsA fd) && !(fdMap containsB fd)) yield {
      val nfd = transformFunDef(fd).getOrElse(fd)
      tmpFdMap += fd -> nfd
      if (fd ne nfd) Some(fd -> nfd) else None
    }).flatten.toMap

    val req: Set[Definition] = {
      val requireCache: MutableMap[Definition, Boolean] = MutableMap.empty
      def required(d: Definition): Boolean = requireCache.getOrElse(d, {
        val res = d match {
          case funDef: FunDef =>
            val (fd, checkBody) = transformedFds.get(funDef) match {
              case Some(fd) => (fd, false)
              case None => (funDef, true)
            }

            val newReturn = transform(fd.returnType)
            lazy val newParams = fd.params.map(vd => ValDef(transform(vd.id)))
            newReturn != fd.returnType || newParams != fd.params || (checkBody && {
              val newBody = transform(fd.fullBody)((fd.params.map(_.id) zip newParams.map(_.id)).toMap)
              newBody != fd.fullBody
            })

          case cd: ClassDef => 
            !(transformedCds contains cd) &&
            (cd.fieldsIds.exists(id => transform(id.getType) != id.getType) ||
              cd.invariant.exists(required))

          case _ => scala.sys.error("Should never happen!?")
        }

        requireCache += d -> res
        res
      })

      val filtered = (cds ++ fds) filter required

      // clear can only take place after all calls to required(_) have taken place
      tmpCdMap.clear()
      tmpFdMap.clear()

      filtered
    }

    val (fdsToDup: Set[FunDef], cdsToDup: Set[ClassDef]) = {
      val prevTransformed = cdMap.aSet.filter(a => a ne cdMap.toB(a)) ++ fdMap.aSet.filter(a => a ne fdMap.toB(a))
      val reqs = req ++ transformedCds.keys ++ transformedFds.keys ++ prevTransformed

      val cdsToDup = cds filter { cd => req(cd) ||
        (!(transformedCds contains cd) && (dependencies(cd) & reqs).nonEmpty) ||
        ((transformedCds contains cd) && ((cd.root +: cd.root.knownDescendants).toSet & req).nonEmpty) }

      val fdsToDup = fds filter (fd => req(fd) || {
        val deps = dependencies(fd)
        (deps exists { case cd: ClassDef => cdsToDup(cd) case _ => false }) ||
        (!(transformedFds contains fd) && (deps & reqs).nonEmpty) })

      (fdsToDup, cdsToDup)
    }

    val fdsToTransform = (transformedFds.keys filterNot fdsToDup).toSet
    val cdsToTransform = (transformedCds.keys filterNot cdsToDup).toSet

    val fdsToKeep = fds filterNot (fd => fdsToDup(fd) || fdsToTransform(fd))
    val cdsToKeep = cds filterNot (cd => cdsToDup(cd) || cdsToTransform(cd))

    fdMap ++= fdsToKeep.map(fd => fd -> fd) ++ fdsToTransform.map(fd => fd -> transformedFds(fd))
    cdMap ++= cdsToKeep.map(cd => cd -> cd) ++ cdsToTransform.map(cd => cd -> transformedCds(cd))

    def duplicateCd(cd: ClassDef): ClassDef = cdMap.cachedB(cd) {
      val parent = cd.parent.map(act => act.copy(classDef = duplicateCd(act.classDef).asInstanceOf[AbstractClassDef]))
      transformedCds.getOrElse(cd, cd) match {
        case acd: AbstractClassDef => acd.duplicate(id = transformId(acd.id, true), parent = parent)
        case ccd: CaseClassDef => ccd.duplicate(id = transformId(ccd.id, true), parent = parent)
      }
    }

    def duplicateFd(fd: FunDef): FunDef = fdMap.cachedB(fd) {
      val ffd = transformedFds.getOrElse(fd, fd)
      val newId = transformId(ffd.id, true)
      val newReturn = transform(ffd.returnType)
      val newParams = ffd.params map (vd => ValDef(transformId(vd.id, true)))
      ffd.duplicate(id = newId, params = newParams, returnType = newReturn)
    }

    for (cd <- cdsToDup) duplicateCd(cd)
    for (fd <- fdsToDup) duplicateFd(fd)

    for (cd <- cdsToDup ++ cdsToTransform) {
      val newCd = cdMap.toB(cd)
      cd.invariant.foreach(fd => newCd.setInvariant(transform(fd)))
      newCd match {
        case (newCcd: CaseClassDef) =>
          if(!fieldsSet(newCcd)) {
            //newCcd is duplicated from the original ccd, so it will always have defined fields,
            //and they will the same as the original ccd fields.
            newCcd.setFields(newCcd.fields.map(vd => ValDef(transformId(vd.id, true))))
            fieldsSet += newCcd
          }
        case _ =>
      }
    }

    for (fd <- fdsToDup ++ fdsToTransform) {
      val nfd = fdMap.toB(fd)
      val bindings = (fd.params zip nfd.params).map(p => p._1.id -> p._2.id).toMap ++
        nfd.params.map(vd => vd.id -> vd.id)

      nfd.fullBody = transform(nfd.fullBody)(bindings)
    }
  }
}

