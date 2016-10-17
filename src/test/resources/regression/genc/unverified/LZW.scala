/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.proof._
import leon.annotation.{ extern, inline, cCode }

import leon.io.{
  FileInputStream => FIS,
  FileOutputStream => FOS,
  StdOut
}

object LZW {

  // GENERAL NOTES
  // =============
  //
  // Encoding using fixed size of word;
  // Input alphabet is the ASCII range (0-255); // 1-26
  // A word is made of 16 bits (instead of the classic 12-bit scenario, for simplicity);
  // The dictionary is an array of 32-bit integers where the index is the key;
  // TODO s/index/codeword
  // TODO 16-bit integers would be useful here!;

  // We limit the size of the dictionary to 2^10
  @inline
  val DICTIONARY_SIZE = 1024

  // We use fix-sized buffers
  @inline
  val BUFFER_SIZE = 10 // characters

  @inline
  val MAX_ARRAY_SIZE = 2048 // Not sure if relevent

  @inline
  val MAX_INT_VALUE = 26

  @inline
  val MIN_INT_VALUE = 1 // 0 is for EOF

  @inline
  val ALPHABET_SIZE = MAX_INT_VALUE - MIN_INT_VALUE

  // TODO reading cannot fail ATM. We assume reading 0 means EOF
  @inline
  val EOF = 0

  private def leammaArraySizes: Boolean = {
    DICTIONARY_SIZE <= MAX_ARRAY_SIZE && DICTIONARY_SIZE > 0 &&
    BUFFER_SIZE <= MAX_ARRAY_SIZE && BUFFER_SIZE > 0 &&
    DICTIONARY_SIZE > ALPHABET_SIZE // min number of elements
  }.holds

  // A buffer representation using a fix-sized array for memory.
  //
  // NOTE Use `createBuffer()` to get a new buffer; don't attempt to create one yourself.
  //
  // NOTE please don't edit length from outside Buffer!
  case class Buffer(val array: Array[Int], var length: Int) {
    require(array.length > 0 && array.length <= MAX_ARRAY_SIZE && length >= 0 && length <= array.length)

    def isEqual(b: Buffer): Boolean = {
      if (b.length != length) false
      else {
        var i = 0
        var matching = true

        while (matching && i < length) {
          if (array(i) != b.array(i))
            matching = false

          i = i + 1
        }

        matching
      }
    }

    def apply(index: Int): Int = {
      require(index >= 0 && index < length)
      array(index)
    }

    def append(x: Int): Unit = {
      require(notFull)

      array(length) = x

      length = length + 1
    } ensuring { u =>
      length <= maxLength
    }

    def dropLast(): Unit = {
      require(length > 0)

      length = length - 1
    } ensuring { u =>
      length >= 0
    }

    def clear(): Unit = {
      length = 0
    } ensuring { u =>
      isEmpty
    }

    def set(b: Buffer) {
      require(array.length >= b.length)
      length = b.length

      var i = 0
      while (i < length) {
        array(i) = b.array(i)
        i = i + 1
      }
    }

    def maxLength: Int = array.length

    def isFull: Boolean = length == maxLength

    def notFull: Boolean = length >= 0 && length < maxLength

    def isEmpty: Boolean = length == 0

    def nonEmpty: Boolean = length >= 0

  }

  @inline // very important because we cannot return arrays
  def createBuffer(): Buffer = {
    Buffer(Array.fill(BUFFER_SIZE)(0), 0)
  } ensuring { b => b.isEmpty && b.notFull }

  // Read the given input file `fis`, encode its content, save the encoded
  // version into `fos`, and return true on success.
  //
  // The algorithm is:
  //  0a. init the dictionary to support the full input alphabet
  //  0b. set P to empty (P below is our `buffer`)
  //  1. read the next character C (a.k.a. `current`)
  //  2. append C to P (i.e. "P = P :: C")
  //  3. check if the dictionary has an entry for the current buffer P
  //    4.  if yes, keep the buffer P as is (i.e. with C at the end)
  //    5a. if not, remove C from the buffer P,
  //    5b.         output the codeword associated with P
  //    5c.         insert "P :: C" into the dictionary to create a new codeword
  //    5d.         set P to the monocharacter string C
  //  6. goto 1 if more characters available
  //  7. P is non empty! So find the corresponding codeword and output it
  def encode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen)

    // 0a. Init dictionary with all basic range
    val (dict, idx) = initDictionary()
    var nextIndex = idx

    // 0b. Create an empty buffer
    val buffer = createBuffer()

    // 1. Read the next input
    // TODO we need to be able to read Byte!
    var current = readByteAsInt(fis)

    // We cannot use `return` to shortcircuit the function and do an early exit,
    // so we keep an abort boolean and use if-statements to wrap actions.
    var abort = false

    (
      while (!abort && current != EOF) {
        // 2. Append input to the buffer
        buffer.append(current)

        // 3. Check if the entry is known
        val (found, index) = findIndex(dict, nextIndex, buffer)

        if (!found) {
          // 5a. Restore previous buffer
          buffer.dropLast()

          // 5b. Output the current codeword
          val (found2, index2) = findIndex(dict, nextIndex, buffer)
          assert(found2)
          if (!outputCodeword(index2, fos))
            abort = true

          // 5c. Insert the extended codeword in the dictionary
          buffer.append(current)
          nextIndex = insertWord(nextIndex, buffer, dict)

          // 5d. Prepare buffer for next round
          buffer.clear()
          buffer.append(current)
        }
        // else: 4. Noop

        // Gracefully exit if we cannot encode the next byte
        if (buffer.isFull || nextIndex == dict.length)
          abort = true

        // 6. Read next char for next while loop iteration
        current = readByteAsInt(fis)
      }
    )

    assert(buffer.nonEmpty)
    assert((!abort) ==> (current == EOF))

    // 7. Process the remaining buffer
    if (!abort) {
      val (found, index) = findIndex(dict, nextIndex, buffer)
      // Either at step 3 the buffer was:
      //  - found in the dictionary and the buffer was not altered (we just read EOF), or
      //  - not found in the dictionary and therefore the buffer now contains only one character.
      assert(found)

      if (!outputCodeword(index, fos))
        abort = true
    }

    // Add EOF marker
    abort = abort || !fos.write(EOF)

    !abort
  }

  // Read the given input file `fis`, decode its content, save the decoded
  // version into `fos`, and return true on success.
  //
  // The algorithm is:
  //  0a. init the dictionary to support the full input alphabet
  //  0b. create a buffer, w
  //  1.  read the next codeword c
  //  2a. if not EOF:
  //  2b.   append c to w
  //  2c.   output c
  //  2d.   read the next codeword c
  //  3.  if EOF stop
  //  4a.  if c is in dictionary (i.e. c < |dict|), set entry to the corresponding value
  //  4b.  else if c == |dict|, set entry to w, then append the first character of w to entry
  //  4c.  else abort (decoding error)
  //  5.  output entry
  //  6a. set tmp to w and then append the first character of entry to tmp
  //  6b. add tmp at the end of the dictionary
  //  7.  set w to entry
  //  8.  goto 4 if more codewords available
  def decode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen)

    // 0a. Init dictionary with all basic range
    val (dict, idx) = initDictionary()
    var nextIndex = idx

    // 0b. Create an empty buffer
    val w = createBuffer()

    // 1. Read the next input
    // TODO we need to be able to read Byte!
    var c = readCodeword(fis)

    // We cannot use `return` to shortcircuit the function and do an early exit,
    // so we keep an abort boolean and use if-statements to wrap actions.
    var abort = false

    // 2a-2d: process the first codeword
    if (c != EOF) {
      w.append(c)
      abort = !outputBuffer(w, fos)
      c = readCodeword(fis)
    }

    // Process the remaining codewords
    while (!abort && c != EOF) {
      // 4a-4c: process current codeword
      val entry = createBuffer()
      if (c < nextIndex) {
        entry.set(dict(c))
      } else if (c == nextIndex) {
        entry.set(w)
        entry.append(w(0))
      } else {
        abort = true
      }

      // Make sure we haven't used the full buffer w or we won't be able to append something;
      // Gracefully exit if we cannot decode the next codeword;
      // 5. output the current entry
      abort = abort || w.isFull || nextIndex == dict.length || !outputBuffer(entry, fos)

      if (!abort) {
        // 6a-6b. augment the dictionary
        val tmp = createBuffer()
        tmp.set(w)
        tmp.append(entry(0))
        nextIndex = insertWord(nextIndex, tmp, dict)

        // 7. prepare for next codeword
        w.set(entry)

        // 8. if more codewords available, process them
        c = readCodeword(fis)
      }
    }

    // Add EOF marker
    abort = abort || !fos.write(EOF)

    !abort
  }

  def outputCodeword(index: Int, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fos.isOpen)
    fos.write(index) && fos.write(" ")
  }

  def outputBuffer(b: Buffer, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fos.isOpen)

    var i = 0
    var success = true

    while (success && i < b.length) {
      success = fos.write(b(i)) && fos.write(" ")
      i = i + 1
    }

    success
  }

  // TODO wrap dictionary into a class?

  // Init the dictionary with the ASCII range encoding and return the next free index in the dictionary
  @inline
  def initDictionary(): (Array[Buffer], Int) = {
    val dict = Array.fill(DICTIONARY_SIZE) { createBuffer() }

    var i = 0

    while (i <= MAX_INT_VALUE) {
      dict(i).append(i)

      i = i + 1
    }

    (dict, i)
  }

  // Attempt to find `buffer` in the given `dict`.
  // Return (true, idx) if found, otherwise (false, _).
  def findIndex(dict: Array[Buffer], dictSize: Int, buffer: Buffer): (Boolean, Int) = {
    var idx = 0
    var found = false

    while (!found && idx < dictSize) {

      if (dict(idx).isEqual(buffer))
        found = true
      else
        idx = idx + 1
    }

    (found, idx)
  }

  // Insert a given word (`buffer`) into `dict` at the given `index` and return the next index
  def insertWord(index: Int, buffer: Buffer, dict: Array[Buffer]): Int = {
    require(0 <= index && index < dict.length)
    dict(index).set(buffer)
    index + 1
  }

  def isValidInput(x: Int) = x >= MIN_INT_VALUE && x <= MAX_INT_VALUE

  def readByteAsInt(fis: FIS)(implicit state: leon.io.State): Int = {
    require(fis.isOpen)
    val x = fis.readInt

    // huhu, I'm clearly cheating here!!!
    if (x < 0) 0 // 0 and not MAX_INT_VALUE as we need to handle EOF
    else if (x > MAX_INT_VALUE) MAX_INT_VALUE
    else x
  } ensuring { res => res == EOF || isValidInput(res) }

  def readCodeword(fis: FIS)(implicit state: leon.io.State): Int = {
    require(fis.isOpen)
    fis.readInt
  }


  @inline
  val SUCCESS = 0

  @inline
  val OPEN_ERROR = -1

  @inline
  val ENCODE_ERROR = 1

  @inline
  val DECODE_ERROR = 2

  def _main() = {
    implicit val state = leon.io.newState


    def status(x: Int): Int = {
      x match {
        case x if x == SUCCESS => StdOut.println("success")
        case x if x == OPEN_ERROR => StdOut.println("couldn't open file")
        case x if x == ENCODE_ERROR => StdOut.println("encoding failed")
        case x if x == DECODE_ERROR => StdOut.println("decoding failed")
        case _ => StdOut.print("unknown error "); StdOut.println(x)
      }

      x
    }

    def encodeFile(): Int = {
      val input = FIS.open("input.txt")
      val encoded = FOS.open("encoded.txt")

      val res =
        if (input.isOpen && encoded.isOpen) {
          if (encode(input, encoded)) status(SUCCESS)
          else status(ENCODE_ERROR)
        } else status(OPEN_ERROR)

      encoded.close
      input.close

      res
    }

    def decodeFile(): Int = {
      val encoded = FIS.open("encoded.txt")
      val decoded = FOS.open("decoded.txt")

      val res =
        if (encoded.isOpen && decoded.isOpen) {
          if (decode(encoded, decoded)) status(SUCCESS)
          else status(DECODE_ERROR)
        } else status(OPEN_ERROR)

      decoded.close
      encoded.close

      res
    }

    val r1 = encodeFile()
    if (r1 == SUCCESS) decodeFile()
    else r1
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

