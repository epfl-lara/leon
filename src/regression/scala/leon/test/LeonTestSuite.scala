/* Copyright 2009-2015 EPFL, Lausanne */

package leon.test

import leon._
import leon.LeonContext
import leon.utils._

import scala.io.Source
import org.scalatest._
import org.scalatest.time.Span
import org.scalatest.concurrent._
import org.scalatest.time.SpanSugar._
import org.scalatest.exceptions.TestFailedException

import java.io.File

trait LeonTestSuite extends FunSuite with Timeouts with BeforeAndAfterEach {
  // Hard-code resource directory, for Eclipse purposes
  val resourceDirHard = "src/test/resources/"

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
      val id = testIdentifier(name)

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


  def resourceDir(dir : String) : File = {

    val d = this.getClass.getClassLoader.getResource(dir)

    if(d == null || d.getProtocol != "file") {
      // We are in Eclipse. The only way we are saved is by hard-coding the path
      new File(resourceDirHard + dir)
    }
    else {
      new File(d.toURI)
    }
  }


  
  
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

    val d = this.getClass.getClassLoader.getResource(dir)

    val asFile = if(d == null || d.getProtocol != "file") {
      // We are in Eclipse. The only way we are saved is by hard-coding the path
      new File(resourceDirHard + dir)
    } else new File(d.toURI)

    scanFilesIn(asFile, filter, recursive)
  }
}
