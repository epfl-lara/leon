package leon.test
import scala.io.Source
import org.scalatest._

import java.io.File

trait LeonTestSuite extends FunSuite {
  def now() = {
    System.currentTimeMillis
  }

  case class Statistics(values: List[Long]) {
    val n      = values.size
    val avg    = values.sum.toDouble/n
    val stddev = Math.sqrt(Math.abs(values.map(_.toDouble - avg).sum/n))

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

  def testIdentifier(name: String): String = {
    (this.getClass.getName+"-"+name).replaceAll("[^0-9a-zA-Z-]", "")
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

  override def test(name: String, tags: Tag*)(body: => Unit) {
    super.test(name, tags: _*) {
      val id = testIdentifier(name)
      val ts = now()

      body

      val total = now()-ts

      val stats = getStats(id)

      if (!stats.accountsFor(total)) {
        fail("Test took too long to run: "+total+"ms (avg: "+stats.avg+", stddev: "+stats.stddev+")")
      }

      storeStats(id, stats.withValue(total))
    }
  }

  private val all : String=>Boolean = (s : String) => true

  def filesInResourceDir(dir : String, filter : String=>Boolean = all) : Iterable[File] = {
    import scala.collection.JavaConversions._

    val d = this.getClass.getClassLoader.getResource(dir)

    if(d == null || d.getProtocol != "file") {
      assert(false, "Tests have to be run from within `sbt`, for otherwise the test files will be harder to access (and we dislike that).")
    }

    val asFile = new File(d.toURI())

    asFile.listFiles().filter(f => filter(f.getPath()))
  }
}
