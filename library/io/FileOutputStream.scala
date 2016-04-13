/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._
import leon.lang.Option

// FIXME Importing leon.lang.Option doesn't mean it is imported, why?
//
// FIXME I couldn't use java.io.FileOutputStream as a field of FileOutputStream... Leon doesn't
//       accept it. Instead, the stream is opened and closed everytime an operation is
//       carried out. Not efficient but better than nothing. The C99 implementation doesn't
//       suffer from this issue.
//
// NOTE Don't attempt to create a FileOutputStream directly. Use FileOutputStream.open instead.
//
// NOTE Don't forget to close the stream.

@library
@cCode.typedef(alias = "FILE*", include = "stdio.h")
case class FileOutputStream(var filename: Option[String])

@library
object FileOutputStream {

  /**
   * Open a new stream to write into `filename`, erasing any previous
   * content of the file or creating a new one if needed.
   */
  @extern
  @cCode.function(code =
    """
    |FileOutputStream __FUNCTION__(char* filename) {
    |  FileOutputStream stream = fopen(filename, "w");
    |  // stream == NULL on failure
    |  return stream;
    |}
    """
  )
  def open(filename: String): FileOutputStream = {
    new FileOutputStream(
      try {
        // Check whether the stream can be opened or not
        val out = new java.io.FileOutputStream(filename)
        out.close()
        leon.lang.Some[String](filename)
      } catch {
        case _: Throwable => leon.lang.None[String]
      }
    )
  }

  /**
   * Close the stream; return `true` on success.
   *
   * NOTE The stream must not be used afterward, even on failure.
   */
  @cCode.function(code =
    """
    |bool __FUNCTION__(FileOutputStream stream) {
    |  if (stream != NULL)
    |    return fclose(stream) == 0;
    |  else
    |    return true;
    |}
    """
  )
  def close(stream: FileOutputStream): Boolean = {
    stream.filename = leon.lang.None[String]
    true // This implementation never fails
  }

  /**
   * Test whether the stream is opened or not.
   *
   * NOTE This is a requirement for all write operations.
   */
  @cCode.function(code =
    """
    |bool __FUNCTION__(FileOutputStream stream) {
    |  return stream != NULL;
    |}
    """
  )
  // We assume the stream to be opened if and only if the filename is defined;
  // see FileStream.open factory method.
  def isOpen(stream: FileOutputStream) = stream.filename.isDefined

  /**
   * Append an integer to the stream and return `true` on success.
   *
   * NOTE The stream must be opened first.
   */
  @extern
  @cCode.function(code =
    """
    |bool __FUNCTION__(FileOutputStream stream, int32_t x) {
    |  return fprintf(stream, "%"PRIi32, x) >= 0;
    |}
    """,
    includes = "inttypes.h"
  )
  def write(stream: FileOutputStream, x: Int): Boolean = {
    require(isOpen(stream))
    try {
      val out = new java.io.FileOutputStream(stream.filename.get, true)
      out.close()
      true
    } catch {
      case _: Throwable => false
    }
  }
}

