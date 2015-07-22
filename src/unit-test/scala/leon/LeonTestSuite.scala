/* Copyright 2009-2015 EPFL, Lausanne */

package leon

import utils._

import org.scalatest._
import org.scalatest.exceptions.TestFailedException

trait LeonTestSuite extends FunSuite {

  def createLeonContext(opts: String*): LeonContext = {
    val reporter = new TestSilentReporter

    Main.processOptions(opts.toList).copy(reporter = reporter, interruptManager = new InterruptManager(reporter))
  }

  //var testContext: LeonContext = null

  //override def beforeEach() = {
  //  testContext = createLeonContext()
  //  super.beforeEach()
  //}

  //def testIdentifier(name: String): String = {
  //  def sanitize(s: String) = s.replaceAll("[^0-9a-zA-Z-]", "")

  //  sanitize(this.getClass.getName)+"/"+sanitize(name)
  //}

  //def bookKeepingFile(id: String) = {
  //  import java.io.File

  //  val f = new File(System.getProperty("user.dir")+"/.test-history/"+id+".log")

  //  f.getParentFile.mkdirs()

  //  f
  //}

  //def getStats(id: String): Statistics = {
  //  val f = bookKeepingFile(id)

  //  if (f.canRead) {
  //    Statistics(Source.fromFile(f).getLines().flatMap{ line =>
  //      val l = line.trim
  //      if (l.length > 0) {
  //        Some(line.toLong)
  //      } else {
  //        None
  //      }
  //    }.toList)
  //  } else {
  //    Statistics(Nil)
  //  }
  //}

  //def storeStats(id: String, stats: Statistics) {
  //  import java.io.FileWriter

  //  val f = bookKeepingFile(id)

  //  val fw = new FileWriter(f, true)
  //  fw.write(stats.values.head+"\n")
  //  fw.close()
  //}

  //override implicit val defaultInterruptor = new Interruptor {
  //  def apply(t: Thread) {
  //    testContext.interruptManager.interrupt()
  //  }
  //}

  //def testWithTimeout(name: String, timeout: Span)(body: => Unit) {
  //  super.test(name) {
  //    val id = testIdentifier(name)

  //    val ts = now()

  //    failAfter(timeout) {
  //      try {
  //        body
  //      } catch {
  //        case fe: LeonFatalError =>
  //          testContext.reporter match {
  //            case sr: TestSilentReporter =>
  //              sr.lastErrors ++= fe.msg
  //              throw new TestFailedException(sr.lastErrors.mkString("\n"), fe, 5)
  //          }
  //      }
  //    }

  //    val total = now()-ts

  //    val stats = getStats(id)

  //    if (!stats.accountsFor(total)) {
  //      info(Console.YELLOW+"[warning] Test took too long to run: "+total+"ms (avg: "+stats.avg+", stddev: "+stats.stddev+")")
  //    }

  //    storeStats(id, stats.withValue(total))
  //  }
  //}

}
