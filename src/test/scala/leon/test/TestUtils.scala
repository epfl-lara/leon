/* Copyright 2009-2013 EPFL, Lausanne */

package leon
package test

import java.io.File

object TestUtils {
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
