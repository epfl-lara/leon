package leon.solvers.isabelle

import scala.concurrent._
import scala.math.BigInt

import leon.LeonContext
import leon.purescala.Common._
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.purescala.Types._

import edu.tum.cs.isabelle._

case class Constructor(term: Term, disc: Term, sels: Map[ValDef, Term])
case class Datatype(typ: String, constructors: Map[CaseClassDef, Constructor])

object Types {

  def findRoot(typ: ClassType): ClassType =
    typ.parent.map(findRoot).getOrElse(typ)

}

final class Types(context: LeonContext, program: Program, system: System)(implicit ec: ExecutionContext) {

  lazy val char = system.invoke(WordLiteral)(32).assertSuccess(context)

  private val enableMapping = context.findOptionOrDefault(Component.optMapping)

  private val (mapped, unmapped) =
    program.classHierarchyRoots.map { root =>
      val descendants = root match {
        case ccd: CaseClassDef => List(ccd)
        case _ => root.knownDescendants.collect { case ccd: CaseClassDef => ccd }
      }

      root -> descendants
    }.toMap.partition { case (root, descendants) =>
      root.annotations.contains("isabelle.typ") && {
        if (!enableMapping)
          context.reporter.warning(s"Class definition ${root.id} is mapped, but mapping is disabled")
        enableMapping
      }
    }

  private val mappedData: Future[Map[ClassDef, Datatype]] = Future.traverse(mapped) { case (root, descendants) =>
    val name = root.extAnnotations("isabelle.typ") match {
      case List(Some(name: String)) => name
      case List(_) => context.reporter.fatalError(s"In type mapping for class definition ${root.id}: expected a string literal as name")
      case _ => context.reporter.internalError(s"Type mapping for class definition ${root.id}")
    }

    val constructors = descendants.map { desc =>
      val name = desc.extAnnotations.get("isabelle.constructor") match {
        case Some(List(Some(name: String))) => name
        case Some(List(_)) =>
          context.reporter.fatalError(s"In constructor mapping for class definition ${desc.id}: expected a string literal as name")
        case None =>
          context.reporter.fatalError(s"Expected constructor mapping for class definition ${desc.id}, because it inherits from ${root.id} which has a type mapping")
        case Some(_) =>
          context.reporter.internalError(s"Constructor mapping for class definition ${desc.id}")
      }

      (desc.id.mangledName, name)
    }.toList

    system.invoke(LookupDatatype)(name -> constructors).assertSuccess(context).map {
      case Left(err) =>
        context.reporter.fatalError(s"In mapping for class definition ${root.id}: $err")
      case Right(constructors) => root ->
        Datatype(
          typ = name,
          constructors =
            constructors.map { case (name, (term, disc, sels)) =>
              val desc = descendants.find(_.id.mangledName == name).get
              if (desc.fields.length != sels.length)
                context.reporter.fatalError(s"Invalid constructor mapping for ${desc.id}: Isabelle constructor $name has different number of arguments")
              desc -> Constructor(term, disc, (desc.fields, sels).zipped.toMap)
            }.toMap
        )
    }
  }.map(_.toMap)

  def optTyp(tree: Option[TypeTree]): Future[Typ] = tree match {
    case Some(tree) => typ(tree)
    case None => Future.successful(Typ.dummyT)
  }

  def typ(tree: TypeTree, subst: Map[Identifier, Identifier] = Map.empty, strict: Boolean = false): Future[Typ] = {
    def flexary1(constructor: String, ts: Seq[TypeTree]): Future[Typ] =
      Future.traverse(ts.toList)(typ(_, subst, strict)).map(_.reduceRight { (t, acc) => Type(constructor, List(t, acc)) })

    tree match {
      case BooleanType => Future.successful { Type("HOL.bool", Nil) }
      case IntegerType => Future.successful { Type("Int.int", Nil) }
      case UnitType => Future.successful { Type("Product_Type.unit", Nil) }
      case RealType => Future.successful { Type("Real.real", Nil) }
      case CharType => char
      case TypeParameter(id) =>
        val id0 = subst.getOrElse(id, id)
        Future.successful { TFree(s"'${id0.mangledName}", List("HOL.type")) }
      case SetType(base) =>
        typ(base, subst, strict).map { typ => Type("Set.set", List(typ)) }
      case TupleType(bases) =>
        flexary1("Product_Type.prod", bases)
      case FunctionType(args, res) =>
        for {
          r <- typ(res, subst, strict)
          as <- Future.traverse(args)(typ(_, subst, strict))
        }
        yield
          as.foldRight(r) { (t, acc) => Type("fun", List(t, acc)) }
      case bvt: BitVectorType =>
        system.invoke(WordLiteral)(bvt.size).assertSuccess(context)
      case MapType(from, to) =>
        for {
          f <- typ(from, subst, strict)
          t <- typ(to, subst, strict)
        }
        yield
          Type("fun", List(f, Type("Option.option", List(t))))
      case ct: ClassType =>
        val root = Types.findRoot(ct)
        Future.traverse(root.tps.toList) { typ(_, subst, strict) }.flatMap { args =>
          mappedData.map { _.get(root.classDef) match {
            case None => s"$theory.${root.id.mangledName}"
            case Some(datatype) => datatype.typ
          }}.map { Type(_, args) }
        }
      case _ if strict =>
        context.reporter.fatalError(s"Unsupported type $tree, can't be inferred")
      case _ =>
        context.reporter.warning(s"Unknown type $tree, translating to dummy (to be inferred)")
        Future.successful { Typ.dummyT }
    }
  }

  def functionTyp(args: Seq[TypeTree], res: TypeTree): Future[Typ] =
    typ(res).flatMap { res =>
      Future.traverse(args.toList)(typ(_)).map(_.foldRight(res) { (t, acc) => Type("fun", List(t, acc)) })
    }

  private val unmappedData: Future[Map[ClassDef, Datatype]] = {
    val entries = unmapped.map { case (root, descendants) =>
      val name = s"$theory.${root.id.mangledName}"

      if (!enableMapping)
        descendants.foreach { desc =>
          if (desc.annotations.contains("isabelle.constructor"))
            context.reporter.warning(s"Ignoring constructor mapping of class definition ${desc.id}, because its root ${root.id} has no type mapping")
        }

      val constructors = descendants.map { desc => desc ->
        Constructor(
          term = Const(s"$name.c${desc.id.mangledName}", Typ.dummyT),
          disc = Const(s"$name.d${desc.id.mangledName}", Typ.dummyT),
          sels = desc.fields.map { field => field ->
            Const(s"$name.s${field.id.mangledName}", Typ.dummyT)
          }.toMap
        )
      }.toMap

      root -> Datatype(name, constructors)
    }

    val translation = Future.traverse(entries.toList) { case (cls, Datatype(_, constructors)) =>
      val tparams = cls.tparams.map(_.id)
      Future.traverse(constructors.toList) { case (subcls, Constructor(_, _, sels)) =>
        val subst = (subcls.tparams.map(_.id), tparams).zipped.toMap
        Future.traverse(subcls.fields.toList) { field =>
          typ(field.getType, subst, true).map { typ =>
            field.id.mangledName -> typ
          }
        }.map {
          subcls.id.mangledName -> _
        }
      }.map {
        (cls.id.mangledName, tparams.toList.map(_.mangledName), _)
      }
    }

    translation.flatMap(system.invoke(Datatypes)).assertSuccess(context).map {
      case None => entries
      case Some(msg) => context.reporter.fatalError(s"In datatype definition: $msg")
    }
  }

  val data = for { d1 <- mappedData; d2 <- unmappedData } yield d1 ++ d2

}
