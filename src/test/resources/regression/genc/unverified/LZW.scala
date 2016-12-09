/* Copyright 2009-2016 EPFL, Lausanne */

import leon.lang._
import leon.proof._
import leon.annotation._

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
  // Input alphabet is the ASCII range (0-255);
  // A word is made of 16 bits (instead of the classic 12-bit scenario, for simplicity);
  // The dictionary is an array of ??? where the index is the key;
  // TODO s/index/codeword -> better yet: define index2codeword conversion (Int -> (Byte, Byte))
  // TODO 16-bit integers would be useful here!

  // We limit the size of the dictionary to 2^10
  @inline
  val DictionarySize = 1024

  // We use fix-sized buffers
  @inline
  val BufferSize = 10 // characters

  val AlphabetSize = Byte.MaxValue + -Byte.MinValue

  private def lemmaSize: Boolean = {
    DictionarySize >= AlphabetSize &&
    BufferSize > 0 &&
    AlphabetSize > 0 &&
    DictionarySize <= 1000000
  }.holds

  private def lemmaBufferFull(b: Buffer): Boolean = {
    b.isFull == !b.nonFull
  }.holds

  private def lemmaBufferEmpty(b: Buffer): Boolean = {
    b.isEmpty == !b.nonEmpty
  }.holds

  private def lemmaBufferFullEmpty1(b: Buffer): Boolean = {
    b.isFull ==> b.nonEmpty
  }.holds

  private def lemmaBufferFullEmpty2(b: Buffer): Boolean = {
    (BufferSize > 0 && b.isEmpty) ==> b.nonFull
  }.holds

  private def lemmaBufferSelfEqual(b: Buffer): Boolean = {
    b.isEqual(b)
  }.holds

  private def lemmaBufferEqual(a: Buffer, b: Buffer): Boolean = {
    b.isEqual(a) ==> a.isEqual(b)
  }.holds

  private def lemmaBufferEqualImmutable(a: Buffer, b: Buffer): Unit = {
    a.isEqual(b)
  } ensuring { _ => old(a).isEqual(a) && old(b).isEqual(b) }

  private def lemmaDictionaryFull(d: Dictionary): Boolean = {
    d.isFull == !d.nonFull
  }.holds

  private def lemmaDictionaryFullEmpty(d: Dictionary): Boolean = {
    d.isEmpty ==> d.nonFull
  }.holds

  private def lemmaSelfRangeEqual(a: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length)
    isRangeEqual(a, a, from, to) because {
      if (from == to) check { lemmaUnitRangeEqual(a, a, from) }
      else {
        check { a(from) == a(from) } &&
        check { a(to) == a(to) } &&
        check { lemmaSelfRangeEqual(a, from, to - 1) } &&
        check { lemmaSelfRangeEqual(a, from + 1, to) }
      }
    }
  }.holds

  private def lemmaRangeEqual(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)

    ( isRangeEqual(a, b, from, to) ==> isRangeEqual(b, a, from, to) ) // FIXME timeout
  }.holds

  private def lemmaSubRangeEqual1(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)
    isRangeEqual(a, b, from, to) ==> (
      check { a(from) == b(from) } &&
      check { (from + 1 <= to) ==> isRangeEqual(a, b, from + 1, to) }
    )
  }.holds

  private def lemmaSubRangeEqual2(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)
    isRangeEqual(a, b, from, to) ==> (
      check { (a(to) == b(to)) because lemmaRangeEndEqual(a, b, from, to) } &&
      check { (from <= to - 1) ==> isRangeEqual(a, b, from, to - 1) } // FIXME timeout
    )
  }.holds // FIXME TIMEOUT

  private def lemmaMiniSubRangeEqual1(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)
    isRangeEqual(a, b, from, to) ==> (
      isRangeEqual(a, b, from, from) because a(from) == b(from)
    )
  }.holds

  private def lemmaMiniSubRangeEqual2(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)
    isRangeEqual(a, b, from, to) ==> (
      isRangeEqual(a, b, to, to) because {
        if (from == to) check { a(to) == b(to) }
        else {
          check { from < to } &&
          check { lemmaMiniSubRangeEqual2(a, b, from + 1, to) } &&
          check { lemmaMiniSubRangeEqual2(a, b, from, to - 1) }
        }
      }
    )
  }.holds

  private def lemmaUnitRangeEqual(a: Array[Byte], b: Array[Byte], pos: Int): Boolean = {
    require(0 <= pos && pos < a.length && pos < b.length)
    isRangeEqual(a, b, pos, pos) ==> (a(pos) == b(pos))
  }.holds

  private def lemmaRangeEndEqual(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length && isRangeEqual(a, b, from, to))
    ( a(to) == b(to) ) because {
      if (from == to) trivial
      else {
        check { from < to } &&
        check { lemmaRangeEndEqual(a, b, from + 1, to) }
      }
    }
  }.holds


  private def lemmaCodeWordIndexEquality(index: Int): Boolean = {
    require(0 <= index && index < 65536)
    index == codeWord2Index(index2CodeWord(index))
  }.holds


  private def lemmaAllValidBuffers(buffers: Array[Buffer]): Boolean = {
    allValidBuffers(buffers)
  }.holds // FIXME TIMEOUT



  private def testIsRangeEqual(): Boolean = {
    val a = Array[Byte](1, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    val b = Array[Byte](-128, 0, 0, 0, 0, 0, 0, 0, 0, 0)
    !isRangeEqual(a, b, 0, 0)
  }.holds


  private def testBufferIsEqual(): Boolean = {
    val a = createBuffer()
    val b = createBuffer()

    a.append(1)
    b.append(-128)

    assert(a.size == b.size)
    assert(a.nonEmpty)
    assert(b.nonEmpty)
    assert(a.isEmpty == b.isEmpty)

    !a.isEqual(b)
  }.holds

  // Helper for range equality checking
  private def isRangeEqual(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
    require(0 <= from && from <= to && to < a.length && to < b.length)
    a(from) == b(from) && {
      if (from == to) true
      else isRangeEqual(a, b, from + 1, to)
    }
  }


  private def allValidBuffers(buffers: Array[Buffer]): Boolean = {
    def rec(from: Int): Boolean = {
      require(0 <= from && from <= buffers.length)
      if (from < buffers.length) buffers(from).isValid && rec(from + 1)
      else true
    }

    rec(0)
  }


  // A buffer representation using a fix-sized array for memory.
  //
  // NOTE Use `createBuffer()` to get a new buffer; don't attempt to create one yourself.
  case class Buffer(private val array: Array[Byte], private var length: Int) {
    val capacity = array.length
    require(isValid)

    def isValid: Boolean = length >= 0 && length <= capacity && capacity == BufferSize

    def isFull: Boolean = length == capacity

    def nonFull: Boolean = length < capacity

    def isEmpty: Boolean = length == 0

    def nonEmpty: Boolean = length > 0

    def isEqual(b: Buffer): Boolean = {
      if (b.length != length) false
      else { isEmpty || isRangeEqual(array, b.array, 0, length - 1) }
    } //ensuring { _ => this.isEqual(old(this)) && b.isEqual(old(b)) } // this VC does infinite recursion

    def size = length

    def apply(index: Int): Byte = {
      require(index >= 0 && index < length)
      array(index)
    }

    def append(x: Byte): Unit = {
      require(nonFull)

      array(length) = x

      length += 1
    } ensuring { _ => isValid }

    def dropLast(): Unit = {
      require(nonEmpty)

      length -= 1
    } ensuring { _ => isValid } //&& old(this).length == length + 1 }

    def clear(): Unit = {
      length = 0
    } ensuring { _ => isEmpty && isValid }

    def set(b: Buffer): Unit = {
      if (b.isEmpty) clear
      else setImpl(b)
    } ensuring { _ => b.isValid && isValid && isEqual(b) /* && b.isEqual(old(b)) */ }

    private def setImpl(b: Buffer): Unit = {
      require(b.nonEmpty)

      length = b.length

      assert(b.isValid)
      assert(isValid)
      assert(nonEmpty)
      assert(length == b.length)

      var i = 0
      (while (i < length) {
        assert(isValid)
        assert(nonEmpty)
        assert(length == b.length)
        assert(i > 0 ==> isRangeEqual(array, b.array, 0, i - 1))

        array(i) = b.array(i)
        i += 1

        assert(isValid)
        assert(nonEmpty)
        assert(length == b.length)
        assert(i > 0 ==> isRangeEqual(array, b.array, 0, i - 1))
      }) invariant { // FIXME TIMEOUT
        0 <= i && i <= length &&
        // lengthCheckpoint == b.length && lengthCheckpoint == length && // no mutation of the length
        isValid && nonEmpty &&
        length == b.length &&
        (i > 0 ==> isRangeEqual(array, b.array, 0, i - 1)) // avoid OutOfBoundAccess
      }

      assert(b.isValid)
      assert(isValid)
      assert(nonEmpty)
      assert(isRangeEqual(array, b.array, 0, length - 1))
      assert(length == b.length)
      assert(isEqual(b))
    } ensuring { _ => b.isValid && isValid && nonEmpty && isEqual(b) /* && b.isEqual(old(b)) */ }

/*
 *     def set(b: Buffer): Unit = {
 *       require(array.length == b.length) // all buffers have the same capacity
 *
 *       var i = 0
 *       (while (i < b.length) {
 *         array(i) = b.array(i)
 *         i = i + 1
 *       }) invariant {
 *         i >= 0 && i <= b.length &&
 *         array.length >= b.length &&
 *         isRangeEqual(array, b.array, 0, i)
 *       }
 *
 *       length = b.length
 *     } ensuring { _ => this.isEqual(b) }
 */

  }

  /*
   * private def isRangeEqual(a: Array[Byte], b: Array[Byte], from: Int, to: Int): Boolean = {
   *   require(0 <= from && from <= to && to < a.length && a.length == b.length)
   *   if (from == to) true else {
   *     // a(from) == b(from) && (from <= to ==> isRangeEqual(a, b, from + 1, to))
   *   }
   * }
   */

  @inline // very important because we cannot return arrays
  def createBuffer(): Buffer = {
    Buffer(Array.fill(BufferSize)(0), 0)
  } ensuring { b => b.isEmpty && b.nonFull && b.isValid }

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
/*
 *   def encode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
 *     require(fis.isOpen && fos.isOpen)
 *
 *     // 0a. Init dictionary with all basic range
 *     val (dict, idx) = initDictionary()
 *
 *     encodeImpl(fis, fos, dict, idx)
 *   }
 */

/*
 *   def encodeImpl(fis: FIS, fos: FOS, dict: Array[Buffer], idx: Int)(implicit state: leon.io.State): Boolean = {
 *     require(fis.isOpen && fos.isOpen && dict.length == DICTIONARY_SIZE && 0 <= idx && idx <= dict.length && allValidBuffer(dict))
 *
 *     var nextIndex = idx
 *
 *     // 0b. Create an empty buffer
 *     val buffer = createBuffer()
 *
 *     // 1. Read the next input
 *     var current = readByte(fis)
 *
 *     // We cannot use `return` to shortcircuit the function and do an early exit,
 *     // so we keep an abort boolean and use if-statements to wrap actions.
 *     var abort = false
 *
 *     (
 *       while (!abort && current.isDefined) {
 *         // 2. Append input to the buffer
 *         buffer.append(current.get)
 *
 *         // 3. Check if the entry is known
 *         assert(dict.length == DICTIONARY_SIZE)
 *         val index = findIndex(dict, nextIndex, buffer)
 *
 *         if (index.isEmpty) {
 *           // 5a. Restore previous buffer
 *           buffer.dropLast()
 *
 *           // 5b. Output the current codeword
 *           val index2 = findIndex(dict, nextIndex, buffer)
 *           // By construction, the index will be found but this fact is not proven so we have to check for it
 *           if (index2.isEmpty || !outputCodeword(index2.get, fos))
 *             abort = true
 *
 *           // 5c. Insert the extended codeword in the dictionary
 *           buffer.append(current.get)
 *           nextIndex = insertWord(nextIndex, buffer, dict)
 *
 *           // 5d. Prepare buffer for next round
 *           buffer.clear()
 *           buffer.append(current.get)
 *         }
 *         // else: 4. Noop
 *
 *         // Gracefully exit if we cannot encode the next byte
 *         if (buffer.isFull || nextIndex == dict.length)
 *           abort = true
 *
 *         // 6. Read next char for next while loop iteration
 *         current = readByte(fis)
 *       }
 *     ) invariant {
 *       (!abort ==> (buffer.notFull && nextIndex < dict.length)) &&
 *       dict.length == DICTIONARY_SIZE &&
 *       0 <= nextIndex && nextIndex <= dict.length &&
 *       allValidBuffer(dict)
 *     }
 *
 *     // 7. Process the remaining buffer, if any
 *     if (!abort && buffer.nonEmpty) {
 *       assert(dict.length == DICTIONARY_SIZE)
 *       val index = findIndex(dict, nextIndex, buffer)
 *       // Either at step 3 the buffer was:
 *       //  - found in the dictionary and the buffer was not altered (we just read EOF), or
 *       //  - not found in the dictionary and therefore the buffer now contains only one character.
 *       assert(index.isDefined)
 *
 *       if (!outputCodeword(index.get, fos))
 *         abort = true
 *     }
 *
 *     !abort
 *   }
 */

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
/*
 *   def decode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
 *     require(fis.isOpen && fos.isOpen)
 *
 *     // 0a. Init dictionary with all basic range
 *     val (dict, idx) = initDictionary()
 *     var nextIndex = idx
 *
 *     // 0b. Create an empty buffer
 *     val w = createBuffer()
 *
 *     // 1. Read the next input
 *     // TODO we need to be able to read Byte!
 *     var c = readCodeword(fis)
 *
 *     // We cannot use `return` to shortcircuit the function and do an early exit,
 *     // so we keep an abort boolean and use if-statements to wrap actions.
 *     var abort = false
 *
 *     // 2a-2d: process the first codeword
 *     if (c != EOF) {
 *       w.append(c)
 *       abort = !outputBuffer(w, fos)
 *       c = readCodeword(fis)
 *     }
 *
 *     // Process the remaining codewords
 *     while (!abort && c != EOF) {
 *       // 4a-4c: process current codeword
 *       val entry = createBuffer()
 *       if (c < nextIndex) {
 *         entry.set(dict(c))
 *       } else if (c == nextIndex) {
 *         entry.set(w)
 *         entry.append(w(0))
 *       } else {
 *         abort = true
 *       }
 *
 *       // Make sure we haven't used the full buffer w or we won't be able to append something;
 *       // Gracefully exit if we cannot decode the next codeword;
 *       // 5. output the current entry
 *       abort = abort || w.isFull || nextIndex == dict.length || !outputBuffer(entry, fos)
 *
 *       if (!abort) {
 *         // 6a-6b. augment the dictionary
 *         val tmp = createBuffer()
 *         tmp.set(w)
 *         tmp.append(entry(0))
 *         nextIndex = insertWord(nextIndex, tmp, dict)
 *
 *         // 7. prepare for next codeword
 *         w.set(entry)
 *
 *         // 8. if more codewords available, process them
 *         c = readCodeword(fis)
 *       }
 *     }
 *
 *     // Add EOF marker
 *     abort = abort || !fos.write(EOF)
 *
 *     !abort
 *   }
 */

  /*
   * def outputCodeword(index: Int, fos: FOS)(implicit state: leon.io.State): Boolean = {
   *   require(fos.isOpen)
   *   val b2 = index.toByte
   *   val b1 = (index >>> 8).toByte
   *   fos.write(b1) && fos.write(b2)
   * }
   */

/*
 *   def outputBuffer(b: Buffer, fos: FOS)(implicit state: leon.io.State): Boolean = {
 *     require(fos.isOpen)
 *
 *     var i = 0
 *     var success = true
 *
 *     while (success && i < b.length) {
 *       success = fos.write(b(i)) && fos.write(" ")
 *       i = i + 1
 *     }
 *
 *     success
 *   }
 */

  // TODO wrap dictionary into a class?

  // Init the dictionary with the range of Byte and return the next free index in the dictionary
/*
 *   @inline
 *   def initDictionary(): (Array[Buffer], Int) = {
 *     val dict = Array.fill(DICTIONARY_SIZE) { createBuffer() }
 *     assert(dict.length == DICTIONARY_SIZE)
 *     assert(allValidBuffer(dict))
 *     // assert(arrayForall(dict, { buffer: Buffer => buffer.isEmpty && buffer.notFull })) // not supported???
 *
 *     var index = 0
 *     var value: Int = Byte.MinValue // Use an Int to avoid overflow issues
 *
 *     (while (value <= Byte.MaxValue) {
 *       assert(Byte.MinValue <= value && value <= Byte.MaxValue)
 *       assert(dict(index).notFull) // this fails for some reason
 *       dict(index).append(value.toByte) // safe conversion, no loss of information
 *
 *       index += 1
 *       value += 1 // last iteration would overflow on Byte but not on Int
 *     }) invariant {
 *       value >= Byte.MinValue && value <= Byte.MaxValue + 1 &&
 *       index >= 0 && index <= DICTIONARY_SIZE &&
 *       index == value + -Byte.MinValue && // they increment at the same speed
 *       dict.length == DICTIONARY_SIZE &&
 *       allValidBuffer(dict)
 *     }
 *
 *     (dict, index)
 *   } ensuring { res => allValidBuffer(res._1) && res._2 == ALPHABET_SIZE }
 */

  // Attempt to find `buffer` in the given `dict`.
/*
 *   def findIndex(dict: Array[Buffer], dictSize: Int, buffer: Buffer): Option[Int] = {
 *     require(dict.length == DICTIONARY_SIZE && 0 <= dictSize && dictSize <= dict.length && allValidBuffer(dict))
 *
 *     var idx = 0
 *     var found = false
 *
 *     (while (!found && idx < dictSize) {
 *       found = dict(idx).isEqual(buffer)
 *       // idx = idx + 1 // buggy!!! increement only when not found!, counter example was found!!!
 *       if (!found)
 *         idx += 1
 *     }) ensuring {
 *       idx >= 0 && idx <= dictSize
 *     }
 *
 *     if (found) Some[Int](idx) else None[Int]()
 *   } ensuring { res =>
 *     // (res.isDefined == arrayExists(dict, 0, dictSize - 1, { elem: Buffer => elem.isEqual(buffer) })) && // Not supported???
 *     (res.isDefined ==> dict(res.get).isEqual(buffer)) &&
 *     dict.length == DICTIONARY_SIZE
 *   }
 *
 */
  // Insert a given word (`buffer`) into `dict` at the given `index` and return the next index
/*
 *   def insertWord(index: Int, buffer: Buffer, dict: Array[Buffer]): Int = {
 *     require(0 <= index && index < dict.length && dict.length == DICTIONARY_SIZE && allValidBuffer(dict))
 *
 *     dict(index).set(buffer)
 *     index + 1
 *   } ensuring { res =>
 *     0 < res && res <= dict.length &&
 *     dict.length == DICTIONARY_SIZE
 *   }
 */

  def tryReadNext(fis: FIS)(implicit state: leon.io.State): Option[Byte] = {
    require(fis.isOpen)
    fis.tryReadByte()
  }

  def writeCodeWord(fos: FOS, cw: CodeWord): Boolean = {
    require(fos.isOpen)
    fos.write(cw.b1) && fos.write(cw.b2)
  }

  def tryReadCodeWord(fis: FIS)(implicit state: leon.io.State): Option[CodeWord] = {
    require(fis.isOpen)
    val b1Opt = fis.tryReadByte()
    val b2Opt = fis.tryReadByte()

    (b1Opt, b2Opt) match {
      case (Some(b1), Some(b2)) => Some(CodeWord(b1, b2))
      case _ => None()
    }
  }

  def writeBytes(fos: FOS, buffer: Buffer): Boolean = {
    require(fos.isOpen && buffer.nonEmpty)
    var success = true
    var i = 0

    val size = buffer.size

    (while (success && i < size) {
      success = fos.write(buffer(i))
      i += 1
    }) invariant {
      0 <= i && i <= size
    }

    success
  }


  case class CodeWord(b1: Byte, b2: Byte) // a 16-bit code word

  def index2CodeWord(index: Int): CodeWord = {
    require(0 <= index && index < 65536) // unsigned index
    // Shift the index in the range [-32768, 32767] to make it signed
    val signed = index - 32768
    // Split it into two byte components
    val b2 = signed.toByte
    val b1 = (signed >>> 8).toByte
    CodeWord(b1, b2)
  }

  def codeWord2Index(cw: CodeWord): Int = {
    // When building the signed integer back, make sure to understand integer
    // promotion with negative numbers: we need to avoid the signe extension here.
    val signed = (cw.b1 << 8) | (0xff & cw.b2)
    signed + 32768
  } ensuring { res => 0 <= res && res < 65536 }


  case class Dictionary(private val buffers: Array[Buffer], private var nextIndex: Int) {
    val capacity = buffers.length
    require(isValid)

    def isValid = 0 <= nextIndex && nextIndex <= capacity && capacity == DictionarySize && allValidBuffers(buffers)

    def isEmpty = nextIndex == 0

    def nonEmpty = !isEmpty

    def isFull = nextIndex == capacity

    def nonFull = nextIndex < capacity

    def lastIndex = {
      require(nonEmpty)
      nextIndex - 1
    }

    def contains(index: Int): Boolean = {
      require(0 <= index)
      index < nextIndex
    }

    def appendTo(index: Int, buffer: Buffer): Boolean = {
      require(0 <= index && contains(index))

      val size = buffers(index).size

      if (buffer.size + size <= buffer.capacity) {
        assert(buffer.nonFull)

        var i = 0
        (while (i < size) {
          buffer.append(buffers(index)(i))
          i += 1
        }) invariant {
          0 <= i && i <= size &&
          (i < size ==> buffer.nonFull)
        }

        true
      } else false
    }

    def insert(b: Buffer): Unit = {
      require(nonFull && b.nonEmpty)

      assert(lemmaSize)
      assert(isValid)
      assert(nonFull)
      assert(nextIndex < capacity)
      assert(nextIndex < DictionarySize)
      assert(nextIndex + 1 <= DictionarySize)

      buffers(nextIndex).set(b) // FIXME TIMEOUT (?)

      assert(lemmaSize)
      assert(isValid) // FIXME TIMEOUT
      assert(nonFull) // FIXME TIMEOUT
      assert(nextIndex < capacity) // FIXME TIMEOUT
      assert(nextIndex < DictionarySize) // FIXME TIMEOUT
      assert(nextIndex + 1 <= DictionarySize) // FIXME TIMEOUT

      nextIndex += 1 // FIXME TIMEOUT
    } ensuring { _ => isValid } // FIXME TIMEOUT

    def encode(b: Buffer): Option[CodeWord] = {
      require(b.nonEmpty)

      var found = false
      var i = 0

      (while (!found && i < nextIndex) {
        if (buffers(i).isEqual(b)) {
          found = true
        } else {
          i += 1
        }
      }) invariant {
        0 <= i && i <= nextIndex && i <= capacity &&
        isValid &&
        (found ==> (i < nextIndex && buffers(i).isEqual(b)))
      }

      if (found) Some(index2CodeWord(i)) else None()
    }
  }

  @inline // in order to "return" the arrays
  def createDictionary() = {
    Dictionary(Array.fill(DictionarySize){ createBuffer() }, 0)
  } ensuring { res => res.isEmpty }

  def initialise(dict: Dictionary): Unit = {
    require(dict.isEmpty) // initialise only fresh dictionaries

    val buffer = createBuffer()
    assert(buffer.isEmpty)

    var value: Int = Byte.MinValue // Use an Int to avoid overflow issues

    (while (value <= Byte.MaxValue) {
      buffer.append(value.toByte) // no truncation here
      dict.insert(buffer)
      buffer.dropLast()
      value += 1
    }) invariant { // FIXME TIMEOUT
      dict.nonFull &&
      buffer.isEmpty &&
      value >= Byte.MinValue && value <= Byte.MaxValue + 1 // last iteration goes "overflow" on Byte
    }
  } ensuring { _ => dict.isValid && dict.nonEmpty }

  def encode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen)

    // Initialise the dictionary with the basic alphabet
    val dictionary = createDictionary()
    initialise(dictionary)

    // Small trick to move the static arrays outside the main encoding function;
    // this helps analysing the C code in a debugger (less local variables) but
    // it actually has no impact on performance (or should, in theory).
    encodeImpl(dictionary, fis, fos)
  }

  def encodeImpl(dictionary: Dictionary, fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen && dictionary.nonEmpty)

    var bufferFull = false // TODO handle this as a non-fatal thing.
    var ioError = false

    val buffer = createBuffer()
    assert(buffer.isEmpty && buffer.nonFull)

    var currentOpt = tryReadNext(fis)

    // Read from the input file all its content, stop when an error occurs
    // (either output error or full buffer)
    (while (!bufferFull && !ioError && currentOpt.isDefined) {
      val c = currentOpt.get

      assert(buffer.nonFull)
      buffer.append(c)
      assert(buffer.nonEmpty)

      val code = dictionary.encode(buffer)

      val processBuffer = buffer.isFull || code.isEmpty

      if (processBuffer) {
        // Add s (with c) into the dictionary, if the dictionary size limitation allows it
        if (dictionary.nonFull) {
          dictionary.insert(buffer)
        }

        // Encode s (without c) and print it
        buffer.dropLast()
        assert(buffer.nonFull)
        assert(buffer.nonEmpty)
        val code2 = dictionary.encode(buffer)

        assert(code2.isDefined) // (*)
        // To prove (*) we might need to:
        //  - prove the dictionary can encode any 1-length buffer
        //  - the buffer was empty when entering the loop or
        //    that the initial buffer was in the dictionary.
        ioError = !writeCodeWord(fos, code2.get)

        // Prepare for next codeword: set s to c
        buffer.clear()
        buffer.append(c)
        assert(buffer.nonEmpty)
      }

      bufferFull = buffer.isFull

      currentOpt = tryReadNext(fis)
    }) invariant {
      bufferFull == buffer.isFull &&
      ((!bufferFull && !ioError) ==> buffer.nonEmpty) // it might always be true...
    }

    // Process the remaining buffer
    if (!bufferFull && !ioError) {
      val code = dictionary.encode(buffer)
      assert(code.isDefined) // See (*) above.
      ioError = !writeCodeWord(fos, code.get)
    }

    !bufferFull && !ioError
  }

  def decode(fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen)

    // Initialise the dictionary with the basic alphabet
    val dictionary = createDictionary()
    initialise(dictionary)

    decodeImpl(dictionary, fis, fos)
  }

  def decodeImpl(dictionary: Dictionary, fis: FIS, fos: FOS)(implicit state: leon.io.State): Boolean = {
    require(fis.isOpen && fos.isOpen && dictionary.nonEmpty)

    var illegalInput = false
    var ioError = false
    var bufferFull = false

    var currentOpt = tryReadCodeWord(fis)

    val buffer = createBuffer()

    if (currentOpt.isDefined) {
      val cw = currentOpt.get
      val index = codeWord2Index(cw)

      if (dictionary contains index) {
        bufferFull = !dictionary.appendTo(index, buffer)
        ioError = !writeBytes(fos, buffer)
      } else {
        illegalInput = true
      }

      currentOpt = tryReadCodeWord(fis)
    }

    (while (!illegalInput && !ioError && !bufferFull && currentOpt.isDefined) {
      val cw = currentOpt.get
      val index = codeWord2Index(cw)
      val entry = createBuffer()

      if (dictionary contains index) {
        illegalInput = !dictionary.appendTo(index, entry)
      } else if (index == dictionary.lastIndex + 1) {
        entry.set(buffer)
        entry.append(buffer(0))
      } else {
        illegalInput = true
      }

      ioError = !writeBytes(fos, entry)
      bufferFull = buffer.isFull

      if (!bufferFull) {
        val tmp = createBuffer()
        tmp.set(buffer)
        tmp.append(entry(0))
        if (dictionary.nonFull) {
          dictionary.insert(tmp)
        }

        buffer.set(entry)
      }

      currentOpt = tryReadCodeWord(fis)
    }) invariant {
      true
    }


    !illegalInput && !ioError && !bufferFull
  }
  sealed abstract class Status
  case class Success()     extends Status
  case class OpenError()   extends Status
  case class EncodeError() extends Status
  case class DecodeError() extends Status

  implicit def status2boolean(s: Status): Boolean = s match {
    case Success() => true
    case _ => false
  }

  def _main() = {
    implicit val state = leon.io.newState

    def statusCode(s: Status): Int = s match {
      case Success()     => StdOut.println("success");            0
      case OpenError()   => StdOut.println("couldn't open file"); 1
      case EncodeError() => StdOut.println("encoding failed");    2
      case DecodeError() => StdOut.println("decoding failed");    3
    }

    def encodeFile(): Status = {
      val input = FIS.open("input.txt")
      val encoded = FOS.open("encoded.txt")

      val res =
        if (input.isOpen && encoded.isOpen) {
          if (encode(input, encoded)) Success()
          else EncodeError()
        } else OpenError()

      encoded.close
      input.close

      res
    }

    def decodeFile(): Status = {
      val encoded = FIS.open("encoded.txt")
      val decoded = FOS.open("decoded.txt")

      val res =
        if (encoded.isOpen && decoded.isOpen) {
          if (decode(encoded, decoded)) Success()
          else DecodeError()
        } else OpenError()

      decoded.close
      encoded.close

      res
    }

    val r1 = encodeFile()
    statusCode(if (r1) decodeFile() else r1)
  }

  @extern
  def main(args: Array[String]): Unit = _main()

}

