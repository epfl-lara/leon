package leon
package solvers.isabelle

import scala.concurrent._
import scala.math.BigInt
import scala.reflect.NameTransformer

import leon.LeonContext
import leon.purescala.Common.Identifier
import leon.purescala.Definitions._
import leon.purescala.Expressions._
import leon.verification.VC

import edu.tum.cs.isabelle._
import edu.tum.cs.isabelle.api.ProverResult

object `package` {

  val theory = "Leon_Runtime"
  val isabelleVersion = "2015"


  implicit class FutureResultOps[A](val future: Future[ProverResult[A]]) extends AnyVal {
    def assertSuccess(context: LeonContext)(implicit ec: ExecutionContext): Future[A] = future map {
      case ProverResult.Success(a) => a
      case ProverResult.Failure(err: Operation.ProverException) => context.reporter.internalError(err.fullMessage)
      case ProverResult.Failure(err) => context.reporter.internalError(err.getMessage)
    }
  }

  implicit class ListOptionOps[A](val list: List[Option[A]]) extends AnyVal {
    def sequence: Option[List[A]] = list match {
      case Nil => Some(Nil)
      case None :: _ => None
      case Some(x) :: xs => xs.sequence.map(x :: _)
    }
  }

  implicit class IdentifierOps(val id: Identifier) extends AnyVal {
    def mangledName: String =
      NameTransformer.encode(id.name)
        .replace("_", "'u'")
        .replace("$", "'d'")
        .replaceAll("^_*", "")
        .replaceAll("_*$", "")
        .replaceAll("^'*", "") + "'" + id.globalId
  }

  implicit class FunDefOps(val fd: FunDef) extends AnyVal {
    private def name = fd.id.name

    def statement: Option[Expr] = fd.postcondition match {
      case Some(post) =>
        val args = fd.params.map(_.id.toVariable)
        val appliedPost = Application(post, List(FunctionInvocation(fd.typed, args)))
        Some(fd.precondition match {
          case None => appliedPost
          case Some(pre) => Implies(pre, appliedPost)
        })
      case None => None
    }

    def proofMethod(vc: VC, context: LeonContext): Option[String] =
      fd.extAnnotations.get("isabelle.proof") match {
        case Some(List(Some(method: String), Some(kind: String))) =>
          val kinds = kind.split(',')
          if (kinds.contains(vc.kind.name) || kind == "")
            Some(method)
          else {
            context.reporter.warning(s"Ignoring proof hint for function definition $name: only applicable for VC kinds ${kinds.mkString(", ")}")
            None
          }
        case Some(List(Some(method: String), None)) =>
          Some(method)
        case Some(List(_, _)) =>
          context.reporter.fatalError(s"In proof hint for function definition $name: expected a string literal as method and (optionally) a string literal as kind")
        case Some(_) =>
          context.reporter.internalError(s"Proof hint for function definition $name")
        case None =>
          None
      }

    def isLemma: Boolean =
      fd.annotations.contains("isabelle.lemma")

    def checkLemma(program: Program, context: LeonContext): Option[(FunDef, List[FunDef])] = {
      val name = fd.qualifiedName(program)

      def error(msg: String) =
        context.reporter.fatalError(s"In lemma declaration for function definition $name: $msg")

      fd.extAnnotations.get("isabelle.lemma") match {
        case Some(List(Some(abouts: String))) =>
          val refs = abouts.split(',').toList.map { about =>
            program.lookupAll(about) match {
              case List(fd: FunDef) if !fd.isLemma => fd
              case List(_: FunDef) => error(s"lemmas can only be about plain functions, but $about is itself a lemma")
              case Nil | List(_) => error(s"$about is not a function definition")
              case _ => error(s"$about is ambiguous")
            }
          }
          Some(fd -> refs)
        case Some(List(_)) => error("expected a string literal for about")
        case Some(_) => context.reporter.internalError(s"Lemma declaration for function definition $name")
        case None => None
      }
    }
  }

  def canonicalizeOutput(str: String) =
    // FIXME expose this via libisabelle
    // FIXME use this everywhere
    isabelle.Symbol.decode("""\s+""".r.replaceAllIn(str, " "))

  val Prove = Operation.implicitly[(List[Term], Option[String]), Option[String]]("prove")
  val Pretty = Operation.implicitly[Term, String]("pretty")
  val Load = Operation.implicitly[(String, String, List[(String, String)]), List[String]]("load")
  val Report = Operation.implicitly[Unit, List[(String, String)]]("report")
  val Dump = Operation.implicitly[Unit, List[(String, String)]]("dump")
  val Oracle = Operation.implicitly[Unit, Unit]("oracle")
  val Fresh = Operation.implicitly[String, String]("fresh")
  val NumeralLiteral = Operation.implicitly[(BigInt, Typ), Term]("numeral_literal")
  val Cases = Operation.implicitly[((Term, List[(String, Typ)]), (Typ, List[(Term, Term)])), Term]("cases")
  val SerialNat = Operation.implicitly[Unit, Term]("serial_nat")
  val MapLiteral = Operation.implicitly[(List[(Term, Term)], (Typ, Typ)), Term]("map_literal")
  val Functions = Operation.implicitly[(List[(String, List[(String, Typ)], (Term, Typ))]), Option[String]]("functions")
  val Declare = Operation.implicitly[List[String], Unit]("declare")
  val Equivalences = Operation.implicitly[List[(String, String)], List[String]]("equivalences")
  val AssumeEquivalences = Operation.implicitly[List[(String, String)], Unit]("assume_equivalences")
  val Lemmas = Operation.implicitly[List[(String, Term)], List[String]]("lemmas")
  val AssumeLemmas = Operation.implicitly[List[(String, Term)], Unit]("assume_lemmas")
  val WordLiteral = Operation.implicitly[BigInt, Typ]("word_literal")
  val Datatypes = Operation.implicitly[List[(String, List[String], List[(String, List[(String, Typ)])])], Option[String]]("datatypes")
  val LookupDatatype = Operation.implicitly[(String, List[(String, String)]), Either[String, List[(String, (Term, Term, List[Term]))]]]("lookup_datatype")

}
