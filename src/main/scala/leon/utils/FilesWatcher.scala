/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import java.io.File
import java.nio.file._
import scala.collection.JavaConversions._
import java.security.MessageDigest
import java.math.BigInteger

case class FilesWatcher(ctx: LeonContext, files: Seq[File]) {
  val toWatch = files.map(_.getAbsoluteFile).toSet
  val dirs    = toWatch.map(_.getParentFile)

  def onChange(body: => Unit): Unit = {
    val watcher = FileSystems.getDefault.newWatchService()
    dirs foreach (_.toPath.register(watcher, StandardWatchEventKinds.ENTRY_MODIFY))
    var lastHashes = toWatch.map(md5file)

    body
    ctx.reporter.info("Waiting for source changes...")

    while (true) {
      val key = watcher.take()

      val events = key.pollEvents()

      if (events.exists{ _.context match {
        case (p: Path) =>
          dirs exists { dir => toWatch(new File(dir, p.toFile.getName))}
        case e => false
      }}) {
        val currentHashes = toWatch.map(md5file)
        if (currentHashes != lastHashes) {
          lastHashes = currentHashes

          ctx.reporter.info("Detected new version!")
          body
          ctx.reporter.info("Waiting for source changes...")
        }
      }

      key.reset()
    }
  }

  def md5file(f: File): String = {
    val buffer = new Array[Byte](1024)
    val md = MessageDigest.getInstance("MD5")
    try {
      val is = Files.newInputStream(f.toPath)
      var read = 0
      do {
        read = is.read(buffer)
        if (read > 0) {
          md.update(buffer, 0, read)
        }
      } while (read != -1)
      is.close()

      val bytes = md.digest()
      ("%0" + (bytes.length << 1) + "X").format(new BigInteger(1, bytes));
    } catch {
      case _: RuntimeException =>
        ""
    }
  }
}
