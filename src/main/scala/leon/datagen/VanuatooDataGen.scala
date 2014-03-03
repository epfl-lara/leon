/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package datagen

import purescala.Common._
import purescala.Definitions._
import purescala.TreeOps._
import purescala.Trees._
import purescala.TypeTrees._
import purescala.Extractors.TopLevelAnds

import codegen.CompilationUnit
import vanuatoo.{Pattern => VPattern, _}

import evaluators._

class VanuatooDataGen(ctx: LeonContext, p: Program) extends DataGenerator {
  val unit = new CompilationUnit(ctx, p)

  val ints = (for (i <- Set(0, 1, 2, 3)) yield {
    i -> Constructor[Expr, TypeTree](List(), Int32Type, s => IntLiteral(i), ""+i)
  }).toMap

  val booleans = (for (b <- Set(true, false)) yield {
    b -> Constructor[Expr, TypeTree](List(), BooleanType, s => BooleanLiteral(b), ""+b)
  }).toMap

  def intConstructor(i: Int) = ints(i)

  def boolConstructor(b: Boolean) = booleans(b)

  def cPattern(c: Constructor[Expr, TypeTree], args: Seq[VPattern[Expr, TypeTree]]) = {
    ConstructorPattern[Expr, TypeTree](c, args)
  }

  private var constructors   = Map[TypeTree, List[Constructor[Expr, TypeTree]]]()

  private def getConstructorFor(t: CaseClassType, act: AbstractClassType): Constructor[Expr, TypeTree] = {
    // We "up-cast" the returnType of the specific caseclass generator to match its superclass
    getConstructors(t)(0).copy(retType = act)
  }


  private def getConstructors(t: TypeTree): List[Constructor[Expr, TypeTree]] = t match {
    case UnitType =>
      constructors.getOrElse(t, {
        val cs = List(Constructor[Expr, TypeTree](List(), t, s => UnitLiteral(), "()"))
        constructors += t -> cs
        cs
      })

    case at @ ArrayType(sub) =>
      constructors.getOrElse(at, {
        val cs = for (size <- List(0, 1, 2, 5)) yield {
          Constructor[Expr, TypeTree]((1 to size).map(i => sub).toList, at, s => FiniteArray(s).setType(at), at.toString+"@"+size)
        }
        constructors += at -> cs
        cs
      })

    case tt @ TupleType(parts) =>
      constructors.getOrElse(tt, {
        val cs = List(Constructor[Expr, TypeTree](parts, tt, s => Tuple(s).setType(tt), tt.toString))
        constructors += tt -> cs
        cs
      })

    case mt @ MapType(from, to) =>
      constructors.getOrElse(mt, {
        val cs = for (size <- List(0, 1, 2, 5)) yield {
          val subs   = (1 to size).flatMap(i => List(from, to)).toList

          Constructor[Expr, TypeTree](subs, mt, s => FiniteMap(s.grouped(2).map(t => (t(0), t(1))).toSeq).setType(mt), mt.toString+"@"+size)
        }
        constructors += mt -> cs
        cs
      })

    case tp: TypeParameter =>
      constructors.getOrElse(tp, {
        val cs = for (i <- List(1, 2)) yield {
          Constructor[Expr, TypeTree](List(), tp, s => GenericValue(tp, i), tp.id+"#"+i)
        }
        constructors += tp -> cs
        cs
      })

    case act: AbstractClassType =>
      constructors.getOrElse(act, {
        val cs = act.knownCCDescendents.map {
          cct => getConstructorFor(cct, act)
        }.toList

        constructors += act -> cs

        cs
      })

    case cct: CaseClassType =>
      constructors.getOrElse(cct, {
        val c = List(Constructor[Expr, TypeTree](cct.fieldsTypes, cct, s => CaseClass(cct, s), cct.id.name))
        constructors += cct -> c
        c
      })

    case _ =>
      ctx.reporter.error("Unknown type to generate constructor for: "+t)
      Nil
  }

  private def valueToPattern(v: AnyRef, expType: TypeTree): (VPattern[Expr, TypeTree], Boolean) = (v, expType) match {
    case (i: Integer, Int32Type) =>
      (cPattern(intConstructor(i), List()), true)

    case (b: java.lang.Boolean, BooleanType) =>
      (cPattern(boolConstructor(b), List()), true)

    case (cc: codegen.runtime.CaseClass, ct: ClassType) =>
      val r = cc.__getRead()

      unit.jvmClassToLeonClass(cc.getClass.getName) match {
        case Some(ccd: CaseClassDef) =>
          val cct = CaseClassType(ccd, ct.tps)
          val c = ct match {
            case act : AbstractClassType =>
              getConstructorFor(cct, act)
            case cct : CaseClassType =>
              getConstructors(cct)(0)
          }

          val fields = cc.productElements()

          val elems = for (i <- 0 until fields.length) yield {
            if (((r >> i) & 1) == 1) {
              // has been read
              valueToPattern(fields(i), cct.fieldsTypes(i))
            } else {
              (AnyPattern[Expr, TypeTree](), false)
            }
          }

          (ConstructorPattern(c, elems.map(_._1)), elems.forall(_._2))

        case _ =>
          sys.error("Could not retreive type for :"+cc.getClass.getName)
      }

    case (t: codegen.runtime.Tuple, tt @ TupleType(parts)) =>
      val r = t.__getRead()

      val c = getConstructors(tt)(0)

      val elems = for (i <- 0 until t.getArity) yield {
        if (((r >> i) & 1) == 1) {
          // has been read
          valueToPattern(t.get(i), parts(i))
        } else {
          (AnyPattern[Expr, TypeTree](), false)
        }
      }

      (ConstructorPattern(c, elems.map(_._1)), elems.forall(_._2))

    case (gv: GenericValue, t: TypeParameter) =>
      (cPattern(getConstructors(t)(gv.id-1), List()), true)
    case (v, t) =>
      sys.error("Unsupported value, can't paternify : "+v+" ("+v.getClass+") : "+t)
  }

  type InstrumentedResult = (EvaluationResults.Result, Option[vanuatoo.Pattern[Expr, TypeTree]])

  def compile(expression : Expr, argorder : Seq[Identifier]) : Option[Tuple=>InstrumentedResult] = {
    import leon.codegen.runtime.LeonCodeGenRuntimeException
    import leon.codegen.runtime.LeonCodeGenEvaluationException

    try {
      val ttype = TupleType(argorder.map(_.getType))
      val tid = FreshIdentifier("tup").setType(ttype)

      val map = argorder.zipWithIndex.map{ case (id, i) => (id -> TupleSelect(Variable(tid), i+1)) }.toMap

      val newExpr = replaceFromIDs(map, expression)

      val ce = unit.compileExpression(newExpr, Seq(tid))

      Some((args : Tuple) => {
        try {
          val jvmArgs = ce.argsToJVM(Seq(args))

          val result  = ce.evalFromJVM(jvmArgs)

          // jvmArgs is getting updated by evaluating
          val pattern = valueToPattern(jvmArgs(0), ttype)

          (EvaluationResults.Successful(result), if (!pattern._2) Some(pattern._1) else None)
        } catch {
          case e : ClassCastException  =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : ArithmeticException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : ArrayIndexOutOfBoundsException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : LeonCodeGenRuntimeException =>
            (EvaluationResults.RuntimeError(e.getMessage), None)

          case e : LeonCodeGenEvaluationException =>
            (EvaluationResults.EvaluatorError(e.getMessage), None)
        }
      })
    } catch {
      case t: Throwable =>
        ctx.reporter.warning("Error while compiling expression: "+t.getMessage)
        None
    }
  }

  def generateFor(ins: Seq[Identifier], satisfying: Expr, maxValid: Int, maxEnumerated: Int): Iterator[Seq[Expr]] = {
    // Split conjunctions
    val TopLevelAnds(ands) = satisfying

    val runners = ands.map(a => compile(a, ins) match {
      case Some(runner) => Some(runner)
      case None =>
        ctx.reporter.error("Could not compile predicate "+a)
        None
    }).flatten


    val gen = new StubGenerator[Expr, TypeTree]((ints.values ++ booleans.values).toSeq,
                                                Some(getConstructors _),
                                                treatEmptyStubsAsChildless = true)

    var found = Set[Seq[Expr]]()

    /**
     * Gather at most <n> isomoprhic models  before skipping them
     * - Too little means skipping many excluding patterns
     * - Too large means repetitive (and not useful models) before reaching maxEnumerated
     */

    val maxIsomorphicModels = maxValid+1;

    val it  = gen.enumerate(TupleType(ins.map(_.getType)))

    return new Iterator[Seq[Expr]] {
      var total = 0
      var found = 0;

      var theNext: Option[Seq[Expr]] = None

      def hasNext() = {
        if (total == 0) {
          theNext = computeNext()
        }

        theNext != None
      }

      def next() = {
        val res = theNext.get
        theNext = computeNext()
        res
      }


      def computeNext(): Option[Seq[Expr]] = {
        while(total < maxEnumerated && found < maxValid && it.hasNext && !interrupted.get) {
          val model = it.next.asInstanceOf[Tuple]

          if (model eq null) {
            total = maxEnumerated
          } else {
            total += 1

            var failed = false;

            for (r <- runners) r(model) match {
              case (EvaluationResults.Successful(BooleanLiteral(true)), _) =>

              case (_, Some(pattern)) =>
                failed = true;
                it.exclude(pattern)

              case (_, None) =>
                failed = true;
            }

            if (!failed) {
              //println("Got model:")
              //for ((i, v) <- (ins zip model.exprs)) {
              //  println(" - "+i+" -> "+v)
              //}

              found += 1

              if (found % maxIsomorphicModels == 0) {
                it.skipIsomorphic()
              }

              return Some(model.exprs);
            }

            //if (total % 1000 == 0) {
            //  println("... "+total+" ...")
            //}
          }
        }
        None
      }
    }
  }
}
