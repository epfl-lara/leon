/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package theories

import purescala.Common._
import purescala.Expressions._
import purescala.Definitions._
import purescala.Extractors._
import purescala.ExprOps._
import purescala.Types._

import utils._

import scala.collection.mutable.{Map => MutableMap, Set => MutableSet}

trait TheoryEncoder { self =>
  protected val encoder: Encoder
  protected val decoder: Decoder

  private val idMap = new Bijection[Identifier, Identifier]
  private val fdMap = new Bijection[FunDef    , FunDef    ]
  private val cdMap = new Bijection[ClassDef  , ClassDef  ]

  def encode(id: Identifier): Identifier = encoder.transform(id)
  def decode(id: Identifier): Identifier = decoder.transform(id)

  def encode(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = encoder.transform(expr)
  def decode(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = decoder.transform(expr)

  def encode(tpe: TypeTree): TypeTree = encoder.transform(tpe)
  def decode(tpe: TypeTree): TypeTree = decoder.transform(tpe)

  def encode(fd: FunDef): FunDef = encoder.transform(fd)
  def decode(fd: FunDef): FunDef = decoder.transform(fd)

  protected trait Converter extends purescala.TreeTransformer {
    private[TheoryEncoder] val idMap: Bijection[Identifier, Identifier]
    private[TheoryEncoder] val fdMap: Bijection[FunDef    , FunDef    ]
    private[TheoryEncoder] val cdMap: Bijection[ClassDef  , ClassDef  ]

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

    private val deps: MutableMap[Definition, Set[Definition]] = MutableMap.empty
    private val tmpDefs: MutableSet[Definition] = MutableSet.empty

    private class DependencyFinder(var current: Definition) extends purescala.TreeTraverser {
      val deps: MutableMap[Definition, MutableSet[Definition]] = MutableMap.empty
      deps(current) = MutableSet.empty

      private def withCurrent[T](d: Definition)(b: => T): T = {
        if (!(deps contains d)) deps(d) = MutableSet.empty
        val c = current
        current = d
        val res = b
        current = c
        res
      }

      override def traverse(id: Identifier): Unit = traverse(id.getType)

      override def traverse(cd: ClassDef): Unit = if (!deps(current)(cd)) {
        deps(current) += cd
        if (!(Converter.this.deps contains cd) && !(deps contains cd)) {
          for (cd <- cd.root.knownDescendants :+ cd) {
            cd.invariant foreach (fd => withCurrent(cd)(traverse(fd)))
            withCurrent(cd)(cd.fieldsIds foreach traverse)
            cd.parent foreach { p =>
              deps(p.classDef) = deps.getOrElse(p.classDef, MutableSet.empty) + cd
              deps(cd) = deps.getOrElse(cd, MutableSet.empty) + p.classDef
            }
          }
        }
      }

      override def traverse(fd: FunDef): Unit = if (!deps(current)(fd)) {
        deps(current) += fd
        if (!(Converter.this.deps contains fd) && !(deps contains fd)) withCurrent(fd) {
          fd.params foreach (vd => traverse(vd.id))
          traverse(fd.returnType)
          traverse(fd.fullBody)
        }
      }

      def dependencies: Set[Definition] = {
        current match {
          case fd: FunDef => traverse(fd)
          case cd: ClassDef => traverse(cd)
          case _ =>
        }

        for ((d, ds) <- deps) {
          Converter.this.deps(d) = Converter.this.deps.getOrElse(d, Set.empty) ++ ds
        }

        var changed = false
        do {
          for ((d, ds) <- Converter.this.deps.toSeq) {
            val next = ds.flatMap(d => Converter.this.deps.getOrElse(d, Set.empty))
            if (!(next subsetOf ds)) {
              Converter.this.deps(d) = next
              changed = true
            }
          }
        } while (changed)

        Converter.this.deps(current)
      }
    }

    private def dependencies(d: Definition): Set[Definition] = deps.getOrElse(d, {
      new DependencyFinder(d).dependencies
    })

    private def transformDefs(base: Definition): Unit = {
      val deps = dependencies(base)
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
        newCcd.invariant.foreach(fd => ccd.setInvariant(transform(fd)))
      }

      for (fd <- requiredFds) {
        val nfd = fdMap.toB(fd)
        fd.fullBody = transform(fd.fullBody)((fd.params zip nfd.params).map(p => p._1.id -> p._2.id).toMap)
      }
    }
  }

  protected class Encoder extends Converter {
    private[TheoryEncoder] final val idMap: Bijection[Identifier, Identifier] = TheoryEncoder.this.idMap
    private[TheoryEncoder] final val fdMap: Bijection[FunDef    , FunDef    ] = TheoryEncoder.this.fdMap
    private[TheoryEncoder] final val cdMap: Bijection[ClassDef  , ClassDef  ] = TheoryEncoder.this.cdMap
  }

  protected class Decoder extends Converter {
    private[TheoryEncoder] final val idMap: Bijection[Identifier, Identifier] = TheoryEncoder.this.idMap.swap
    private[TheoryEncoder] final val fdMap: Bijection[FunDef    , FunDef    ] = TheoryEncoder.this.fdMap.swap
    private[TheoryEncoder] final val cdMap: Bijection[ClassDef  , ClassDef  ] = TheoryEncoder.this.cdMap.swap
  }

  def >>(that: TheoryEncoder): TheoryEncoder = new TheoryEncoder {
    val encoder = new Encoder {
      override def transform(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = {
        val mapSeq = bindings.toSeq
        val intermediate = mapSeq.map { case (id, _) => id.duplicate(tpe = self.encoder.transform(id.getType)) }
        val e2 = self.encoder.transform(expr)((mapSeq zip intermediate).map { case ((id, _), id2) => id -> id2 }.toMap)
        that.encoder.transform(e2)((intermediate zip mapSeq).map { case (id, (_, id2)) => id -> id2 }.toMap)
      }

      override def transform(tpe: TypeTree): TypeTree = that.encoder.transform(self.encoder.transform(tpe))

      override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = {
        val (pat2, bindings) = self.encoder.transform(pat)
        val (pat3, bindings2) = that.encoder.transform(pat2)
        (pat3, bindings2.map { case (id, id2) => id -> bindings2(id2) })
      }
    }

    val decoder = new Decoder {
      override def transform(expr: Expr)(implicit bindings: Map[Identifier, Identifier]): Expr = {
        val mapSeq = bindings.toSeq
        val intermediate = mapSeq.map { case (id, _) => id.duplicate(tpe = self.decoder.transform(id.getType)) }
        val e2 = that.decoder.transform(expr)((mapSeq zip intermediate).map { case ((id, _), id2) => id -> id2 }.toMap)
        self.decoder.transform(e2)((intermediate zip mapSeq).map { case (id, (_, id2)) => id -> id2 }.toMap)
      }

      override def transform(tpe: TypeTree): TypeTree = self.decoder.transform(that.decoder.transform(tpe))

      override def transform(pat: Pattern): (Pattern, Map[Identifier, Identifier]) = {
        val (pat2, bindings) = that.decoder.transform(pat)
        val (pat3, bindings2) = self.decoder.transform(pat2)
        (pat3, bindings.map { case (id, id2) => id -> bindings2(id2) })
      }
    }
  }
}

object NoEncoder extends TheoryEncoder {
  val encoder = new Encoder
  val decoder = new Decoder
}

