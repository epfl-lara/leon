/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import leon._
import leon.utils._

import org.scalatest._
import org.scalatest.time.Span
import org.scalatest.concurrent._
import org.scalatest.time.SpanSugar._
import org.scalatest.exceptions.TestFailedException

import java.io.File

trait LeonRegressionSuite extends FunSuite with Timeouts with BeforeAndAfterEach {

  val regressionTestDirectory = "src/test/resources"

  def createLeonContext(opts: String*): LeonContext = {
    val reporter = new TestSilentReporter

    Main.processOptions(opts.toList).copy(reporter = reporter, interruptManager = new InterruptManager(reporter))
  }

  var testContext: LeonContext = null

  override def beforeEach() = {
    testContext = createLeonContext()
    super.beforeEach()
  }

  def testIdentifier(name: String): String = {
    def sanitize(s: String) = s.replaceAll("[^0-9a-zA-Z-]", "")

    sanitize(this.getClass.getName)+"/"+sanitize(name)
  }

  override implicit val defaultInterruptor = new Interruptor {
    def apply(t: Thread) {
      testContext.interruptManager.interrupt()
    }
  }

  def testWithTimeout(name: String, timeout: Span)(body: => Unit) {
    super.test(name) {
      failAfter(timeout) {
        try {
          body
        } catch {
          case fe: LeonFatalError =>
            testContext.reporter match {
              case sr: TestSilentReporter =>
                sr.lastErrors ++= fe.msg
                throw new TestFailedException(sr.lastErrors.mkString("\n"), fe, 5)
            }
        }
      }
    }
  }


  override def test(name: String, tags: Tag*)(body: => Unit) {
    testWithTimeout(name, 5.minutes)(body)
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
}
