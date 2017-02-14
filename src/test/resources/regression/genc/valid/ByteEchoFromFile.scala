/* Copyright 2009-2016 EPFL, Lausanne */

import leon.annotation._
import leon.lang._
import leon.io._

object ByteEchoFromFile {

  def _main(): Int = {
    implicit val state = newState

    val in = FileInputStream.open("CODING_GUIDELINES.md")
    val out = FileOutputStream.open("brain.md")

    val res =
      if (in.isOpen && out.isOpen) {
        var b = in.tryReadByte()

        (while (b.isDefined) {
          out.write(b.get)
          StdOut.print(b.get)
          b = in.tryReadByte()
        }) invariant {
          in.isOpen && out.isOpen
        }

        0
      } else 1

    in.close()
    out.close()

    res
  } // no ensuring here because the opening of the files might fail.

  @extern
  def main(args: Array[String]) = _main()

}

