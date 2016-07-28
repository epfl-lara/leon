/* Copyright 2009-2016 EPFL, Lausanne */

package leon.io

import leon.annotation._
import leon.lang.Option

// See NOTEs in StdIn.
//
// NOTE Don't attempt to create a FileInputStream directly. Use FileInputStream.open instead.
//
// NOTE Don't forget to close the stream.

@library
object FileInputStream {

  /**
   * Open a new stream to read from `filename`, if it exists.
   */
  @extern
  @cCode.function(code =
    """
    |FILE* __FUNCTION__(char* filename, void* unused) {
    |  FILE* this = fopen(filename, "r");
    |  // this == NULL on failure
    |  return this;
    |}
    """
  )
  def open(filename: String)(implicit state: State): FileInputStream = {
    state.seed += 1

    // FIXME Importing leon.lang.Option doesn't mean it is imported, why?
    new FileInputStream(
      try {
        // Check whether the stream can be opened or not
        val out = new java.io.FileReader(filename)
        out.close()
        leon.lang.Some[String](filename)
      } catch {
        case _: Throwable => leon.lang.None[String]
      }
    )
  }

}

@library
@cCode.typedef(alias = "FILE*", include = "stdio.h")
case class FileInputStream(var filename: Option[String]) {

  /**
   * Close the stream; return `true` on success.
   *
   * NOTE The stream must not be used afterward, even on failure.
   */
  @cCode.function(code =
    """
    |bool __FUNCTION__(FILE* this, void* unused) {
    |  if (this != NULL)
    |    return fclose(this) == 0;
    |  else
    |    return true;
    |}
    """
  )
  def close(implicit state: State): Boolean = {
    state.seed += 1

    filename = leon.lang.None[String]
    true // This implementation never fails
  }

  /**
   * Test whether the stream is opened or not.
   *
   * NOTE This is a requirement for all write operations.
   */
  @cCode.function(code =
    """
    |bool __FUNCTION__(FILE* this, void* unused) {
    |  return this != NULL;
    |}
    """
  )
  // We assume the stream to be opened if and only if the filename is defined.
  def isOpen(implicit state: State): Boolean = {
    state.seed += 1

    filename.isDefined
  }

  @library
  @cCode.function(code = """
    |int32_t __FUNCTION__(FILE* this, void* unused) {
    |  int32_t x;
    |  fscanf(this, "%"SCNd32, &x);
    |  return x;
    |}
    """
  )
  def readInt(implicit state: State): Int = {
    state.seed += 1
    nativeReadInt
  }

  // Implementation detail
  @library
  @extern
  @cCode.drop
  private def nativeReadInt(implicit state: State): Int = {
    // TODO Using Java or Scala to implement a simple readInt method
    //      mimicing the C API turns out to be relatively complicated.
    0
  } ensuring((x: Int) => true)


}

