/* Copyright 2009-2016 EPFL, Lausanne */

package leon
package utils

import java.io.{File, PrintWriter}
import scala.io.Source

import com.fasterxml.jackson.databind.ObjectMapper
import com.fasterxml.jackson.module.scala.experimental.ScalaObjectMapper
import com.fasterxml.jackson.module.scala.DefaultScalaModule

import java.text._
import java.util.Date

class BenchmarksHistory(file: File) {

  def this(name: String) = {
    this(new File(name))
  }

  val mapper = new ObjectMapper() with ScalaObjectMapper
  mapper.registerModule(DefaultScalaModule)

  private[this] var entries: List[BenchmarkEntry] = {
    if (file.exists) {
      val str = Source.fromFile(file).mkString

      mapper.readValue[List[Map[String, Any]]](str).map(BenchmarkEntry(_))
    } else {
      Nil
    }
  }

  def write(): Unit = {
    val json = mapper.writeValueAsString(entries.map(_.fields))
    val pw = new PrintWriter(file)
    try {
      pw.write(json)
    } finally {
      pw.close()
    }
  }

  def +=(be: BenchmarkEntry) {
    entries :+= be
  }

}

case class BenchmarkEntry(fields: Map[String, Any]) {
  def +(s: String, v: Any) = {
    copy(fields + (s -> v))
  }

  def ++(es: Map[String, Any]) = {
    copy(fields ++ es)
  }
}

object BenchmarkEntry {
  def fromContext(ctx: LeonContext) = {
    val date = new Date()

    BenchmarkEntry(Map(
      "files" -> ctx.files.map(_.getAbsolutePath).mkString(" "),
      "options" -> ctx.options.mkString(" "),
      "date" -> new SimpleDateFormat("yyyy-MM-dd HH:mm:ss").format(date),
      "ts" -> (System.currentTimeMillis() / 1000L)
    ))
  }
}
