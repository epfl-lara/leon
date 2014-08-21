/* Copyright 2009-2014 EPFL, Lausanne */

package leon.test

import leon._
import leon.{LeonContext,Settings}
import leon.utils._

import scala.io.Source
import org.scalatest._
import org.scalatest.concurrent._
import org.scalatest.time.SpanSugar._
import org.scalatest.exceptions.TestFailedException

import java.io.File

trait LeonTestSuite extends FunSuite with Timeouts with BeforeAndAfterEach {
  // Hard-code resource directory, for Eclipse purposes
  val resourceDirHard = "src/test/resources/regression/"
  
  def now() = {
    System.currentTimeMillis
  }

  case class Statistics(values: List[Long]) {
    val n      = values.size
    val avg    = values.sum.toDouble/n
    val stddev = Math.sqrt(values.map(v => Math.pow(v.toDouble - avg, 2)).sum/n)

    def accountsFor(ms: Long) = {
      if (n < 5) {
        true
      } else {
        val msd = ms.toDouble
        (msd < avg + 3*stddev + 20)
      }
    }

    def withValue(v: Long) = this.copy(v :: values)
  }


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

  def bookKeepingFile(id: String) = {
    import java.io.File

    val f = new File(System.getProperty("user.dir")+"/.test-history/"+id+".log");

    f.getParentFile.mkdirs()

    f
  }

  def getStats(id: String): Statistics = {
    val f = bookKeepingFile(id)

    if (f.canRead()) {
      Statistics(Source.fromFile(f).getLines.flatMap{ line =>
        val l = line.trim
        if (l.length > 0) {
          Some(line.toLong)
        } else {
          None
        }
      }.toList)
    } else {
      Statistics(Nil)
    }
  }

  def storeStats(id: String, stats: Statistics) {
    import java.io.FileWriter

    val f = bookKeepingFile(id)

    val fw = new FileWriter(f, true)
    fw.write(stats.values.head+"\n")
    fw.close
  }

  override implicit val defaultInterruptor = new Interruptor {
    def apply(t: Thread) {
      testContext.interruptManager.interrupt()
    }
  }

  override def test(name: String, tags: Tag*)(body: => Unit) {

    super.test(name, tags: _*) {
      val id = testIdentifier(name)

      val ts = now()

      failAfter(5.minutes) {
        try {
          body
        } catch {
          case fe: LeonFatalError =>
          testContext.reporter match {
            case sr: TestSilentReporter =>
              throw new TestFailedException(sr.lastErrors.mkString("\n"), fe, 5)
          }
        }
      }

      val total = now()-ts

      val stats = getStats(id)

      if (!stats.accountsFor(total)) {
        info(Console.YELLOW+"[warning] Test took too long to run: "+total+"ms (avg: "+stats.avg+", stddev: "+stats.stddev+")")
      }

      storeStats(id, stats.withValue(total))
    }
  }

  protected val all : String=>Boolean = (s : String) => true

 
  def resourceDir(dir : String) : File = {
    import scala.collection.JavaConversions._

    val d = this.getClass.getClassLoader.getResource(dir)

    if(d == null || d.getProtocol != "file") {
      // We are in Eclipse. The only way we are saved is by hard-coding the path
      new File(resourceDirHard + dir)
    }
    else {
      new File(d.toURI())
    }
  }


  
  
  def filesInResourceDir(dir : String, filter : String=>Boolean = all) : Iterable[File] = {
    import scala.collection.JavaConversions._

    val d = this.getClass.getClassLoader.getResource(dir)

    val asFile = if(d == null || d.getProtocol != "file") {
      // We are in Eclipse. The only way we are saved is by hard-coding the path
      new File(resourceDirHard + dir)
    } else new File(d.toURI())

    asFile.listFiles().filter(f => filter(f.getPath()))
  }
}
