/* Copyright 2009-2016 EPFL, Lausanne */

package leon.test

import leon._
import leon.utils._

import org.scalatest._
import org.scalatest.concurrent._
import org.scalatest.exceptions.TestFailedException

import java.io.File

trait LeonRegressionSuite extends FunSuite with Timeouts {

  val regressionTestDirectory = "src/test/resources"

  def createLeonContext(opts: String*): LeonContext = {
    val reporter = new TestSilentReporter

    Main.processOptions(opts.toList).copy(reporter = reporter, interruptManager = new InterruptManager(reporter))
  }

  def testIdentifier(name: String): String = {
    def sanitize(s: String) = s.replaceAll("[^0-9a-zA-Z-]", "")

    sanitize(this.getClass.getName)+"/"+sanitize(name)
  }

  override def test(name: String, tags: Tag*)(body: => Unit) {
    super.test(name) {
      try {
        body
      } catch {
        case fe: LeonFatalError =>
          throw new TestFailedException("Uncaught LeonFatalError" + fe.msg.map(": " + _).getOrElse(""), fe, 5)
      }
    }
  }

  protected val all : String=>Boolean = (s : String) => true

  def scanFilesIn(f: File, filter: String=>Boolean = all, recursive: Boolean = false): Iterable[File] = {
    Option(f.listFiles()).getOrElse(Array()).flatMap{f =>
      if (f.isDirectory && recursive) {
        scanFilesIn(f, filter, recursive)   
      } else {
        List(f) 
      }
    }.filter(f => filter(f.getPath)).toSeq.sortBy(_.getPath)
  }

  def filesInResourceDir(dir : String, filter : String=>Boolean = all, recursive: Boolean = false) : Iterable[File] = {

    val baseDir = new File(s"${Build.baseDirectory}/$regressionTestDirectory/$dir")

    scanFilesIn(baseDir, filter, recursive)
  }

  protected def fail(ctx: LeonContext, reason: String, fe: LeonFatalError): Nothing = {
    val omsg = ctx.reporter match {
      case sr: TestSilentReporter =>
        sr.lastErrors ++= fe.msg
        Some((sr.lastErrors ++ fe.msg).mkString("\n"))
      case _ =>
        fe.msg
    }

    val fullError = omsg match {
      case Some(msg) => s"$reason:\n$msg"
      case None => s"$reason"
    }

    throw new TestFailedException(fullError, fe, 5)
  }
}
