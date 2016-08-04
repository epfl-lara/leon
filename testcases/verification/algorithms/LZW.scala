import leon.lang._
import leon.collection._
import leon.annotation._
import leon.proof._
import scala.language.postfixOps
import ListSpecs._

object LZW {
    sealed abstract class Bit
    case object Z extends Bit
    case object O extends Bit

    /** This method attempts to prove
      * the main theorem of the assignment
      */
    def theorem(data: List[Bit], table: List[List[Bit]]): Boolean = {
        require(algorithmProperties(data, table))
        data == decompress(compress(data, table), table)
    }.holds because tableTheorem(data, table)
    
    def tableTheorem(data: List[Bit], table: List[List[Bit]]): Boolean = {
        require(algorithmProperties(data, table))
        def subTableTheorem(subData: List[Bit], cmpTable: List[List[Bit]], subCmpData: List[BigInt], decmpTable: List[List[Bit]]): (List[List[Bit]], List[List[Bit]]) = {
            require(cmpTable == decmpTable && algorithmProperties(subData, cmpTable) &&
                    compressedDataProperties(subCmpData, decmpTable) && algorithmProperties(Nil[Bit](), decmpTable) && 
                    subData.isEmpty == subCmpData.isEmpty)
            
            subData match {
                case Nil() => (cmpTable, decmpTable)
                case Cons(x, xs) => {
                    val cmpStep: (BigInt, List[Bit], List[Bit]) = compressStep(subData, cmpTable)
                    val newCmpTable: List[List[Bit]] = compressStepTable(subData, cmpTable)
                    val decmpStep: (List[Bit], BigInt, List[BigInt]) = decompressStep(subCmpData, decmpTable)
                    val newDecmpTable: List[List[Bit]] = decompressStepTable(subCmpData, decmpTable)
                    
                    subTableTheorem(cmpStep._3, newCmpTable, decmpStep._3, newDecmpTable)
                }
            }
        } ensuring {
            res: (List[List[Bit]], List[List[Bit]]) =>
                    res._1 == res._2 && algorithmProperties(subData, res._1) &&
                    algorithmProperties(Nil[Bit](), res._2)
        }
        val tables: (List[List[Bit]], List[List[Bit]]) = subTableTheorem(data, table, compress(data, table), table)
        tables._1 == tables._2
    }.holds

    /** This method simply compresses
      * 'data' according to the LZW
      * algorithm and returns the final
      * list of indexes
      */
    @induct
    def compress(data: List[Bit], table: List[List[Bit]]): List[BigInt] = {
        require(algorithmProperties(data, table))
        data match {
            /** While data is not Nil():
              * 1- call compressStep         (to get next compressed index)
              * 2- call compressStepTable     (to get new table)
              * 3- call compress recursively, using the above methods'
              * return values as parameters
              */
            case Nil() => Nil[BigInt]()
            case Cons(x, xs) => {
                val cmpStep: (BigInt, List[Bit], List[Bit]) = compressStep(data, table)
                val newTable: List[List[Bit]] = compressStepTable(data, table)
                cmpStep._1 :: compress(cmpStep._3, newTable)
            }
        }
    } ensuring {
        res: List[BigInt] => decompress(res, table) == data && compressedDataProperties(res, table)
    }
    /** POSTCONDITIONS:
      *
      * 1- decompress(res, table) == data
      */

    /** This method performs one
      * compression step and returns a
      * tuple containing:
      *
      * 1- compressed index
      * 2- compressed sequence
      * 3- remaining uncompressed data
      */
    def compressStep(data: List[Bit], table: List[List[Bit]]): (BigInt, List[Bit], List[Bit]) = {
        require(algorithmProperties(data, table))
        @induct
        def subCompressStep(matchedSeqIndex: BigInt, matchedSeq: List[Bit], unmatchedSeq: List[Bit]): (BigInt, List[Bit], List[Bit]) = {
            require(matchedSeq ++ unmatchedSeq == data because appendProperty(matchedSeq, unmatchedSeq) &&
                   (matchedSeq.isEmpty || (uniqueConditions(matchedSeqIndex, matchedSeq, table) && uniqueProperty(matchedSeqIndex, matchedSeq, table))))

            unmatchedSeq match {
                case Nil() => (matchedSeqIndex, matchedSeq, unmatchedSeq)
                case Cons(x, xs) => {
                    val newSeq: List[Bit] = matchedSeq :+ x
                    if (table.contains(newSeq)) subCompressStep(table.indexOf(newSeq), newSeq, xs) else (matchedSeqIndex, matchedSeq, unmatchedSeq)
                }
            }
        } ensuring {
            res: (BigInt, List[Bit], List[Bit]) =>  res._2 ++ res._3 == data because appendProperty(res._2, res._3) &&
                                                    (res._2.isEmpty || uniqueProperty(res._1, res._2, table))
        }
        /** POSTCONDITIONS:
          *
          * 1- matchedSeq ++ unmatchedSeq == data
          * 2- matchedSeq.isEmpty || table.indexOf(matchedSeq) == matchedSeqIndex
          */
        subCompressStep(0, Nil[Bit](), data)
    } ensuring {
        res: (BigInt, List[Bit], List[Bit]) =>  res._2 ++ res._3 == data &&
                                                (data.isEmpty || (uniqueConditions(res._1, res._2, table) && uniqueProperty(res._1, res._2, table) &&
                                                decompressStep(List[BigInt](res._1), table)._1 == res._2))
    }
    /** POSTCONDITIONS:
      *
      * 1- table(res._1) == res._2
      * 2- decompressStep(res._1, table)._1 == res._2
      * 3- res._2 ++ res._3 == data
      */

    /** This method simply calculates
      * the new entry for the table and
      * returns an already updated table
      */
    def compressStepTable(data: List[Bit], table: List[List[Bit]]): List[List[Bit]] = {
        require(algorithmProperties(data, table))
        @induct
        def subCompressStepTable(matchedSeq: List[Bit], unmatchedSeq: List[Bit]): List[Bit] = {
            unmatchedSeq match {
                case Nil() => Nil[Bit]()
                case Cons(x, xs) => {
                    val newSeq: List[Bit] = matchedSeq ++ List[Bit](x)
                    if (table.contains(newSeq)) subCompressStepTable(newSeq, xs) else newSeq
                }
            }
        } ensuring {
            res: List[Bit] => !table.contains(res)
        }
        val newTableEntry: List[Bit] = subCompressStepTable(Nil[Bit](), data)
        updateTable(newTableEntry, table)

    } ensuring {
        res: List[List[Bit]] => algorithmProperties(data, res)
    }
    /** POSTCONDITIONS:
      * 
      * 1- re-check every condition for 'TABLE RULES'
      * 2- check that res contains every element of table (?)
      */

    /** This method simply decompresses
      * 'cmpData' according to the LZW
      * algorithm and returns the final
      * list of Bits
      */
    @induct
    def decompress(cmpData: List[BigInt], table: List[List[Bit]]): List[Bit] = {
        require(compressedDataProperties(cmpData, table) && algorithmProperties(Nil[Bit](), table))
        cmpData match {
            /** While data is not Nil():
              * 1- call decompressStep             (to get next decompressed sequence)
              * 2- call decompressStepTable     (to get new table)
              * 3- call decompress recursively, using the above methods'
              * return values as parameters
              */
            case Nil() => Nil[Bit]()
            case Cons(x, xs) => {
                val decmpStep: (List[Bit], BigInt, List[BigInt]) = decompressStep(cmpData, table)
                val newTable: List[List[Bit]] = decompressStepTable(cmpData, table)
                decmpStep._1 ++ decompress(decmpStep._3, newTable) 
            }
        }
    }

    /** This method performs one
      * decompression step and returns a
      * tuple containing:
      *
      * 1- decompressed sequence
      * 2- decompressed sequence's index
      * 3- remaining compressed data
      */
    def decompressStep(cmpData: List[BigInt], table: List[List[Bit]]): (List[Bit], BigInt, List[BigInt]) = {
        require(cmpData.nonEmpty && isValidIndex(cmpData.head, table) && algorithmProperties(Nil[Bit](), table))
        (table(cmpData.head), cmpData.head, cmpData.tail)
    } ensuring {
        res: (List[Bit], BigInt, List[BigInt]) => uniqueProperty(res._2, res._1, table) &&
                                                  res._2 :: res._3 == cmpData because prependProperty(res._2, res._3)
    }
    /** POSTCONDITIONS:
      *
      * 1- table.indexOf(res._1) == res._2
      * 2- res._2 :: res._3 == cmpData
      */

    /** This method simply calculates
      * the new entry for the table and
      * returns an already updated table
      */
    def decompressStepTable(cmpData: List[BigInt], table: List[List[Bit]]): List[List[Bit]] = {
        require(algorithmProperties(Nil[Bit](), table) &&
                compressedDataProperties(cmpData, table))

        def subDecompressStepTable(): List[Bit] = (cmpData match {
            case Cons(x1, Cons(x2, xs)) => {
                if(isValidIndex(x2, table)) table(x1) :+ table(x2).head
                else table(x1) :+ table(x1).head
            }
            case Nil() => Nil[Bit]()
            case Cons(x, xs) => Nil[Bit]()
        }) ensuring {
            res: List[Bit] => !table.contains(res)
        }
        val newEntry: List[Bit] = subDecompressStepTable()
        updateTable(newEntry, table)
    } ensuring {
        res: List[List[Bit]] => algorithmProperties(Nil[Bit](), res)
    }
    /** POSTCONDITIONS:
      * 
      * 1- re-check every condition for 'TABLE RULES'
      * 2- check that res contains every element of table
      */

    /** ----------------------
      *   Auxiliary Methods
      * ----------------------
      */
    def updateTable(newEntry: List[Bit], table: List[List[Bit]]): List[List[Bit]] = {
        require(algorithmProperties(Nil[Bit](), table) && !table.contains(newEntry))
        newEntry match {
            case Nil() => table
            case Cons(x, xs) => table :+ newEntry
        }
    } ensuring {
        res: List[List[Bit]] => table.forall(tableElement => res.contains(tableElement) && algorithmProperties(Nil[Bit](), res))
    }
    /** POSTCONDITIONS:
      * 
      * 1- check that res contains every element of table
      */

    /** ALGORITHM RULES:
    * 
    * 1- Table cannot be Nil()
    * 2- Table cannot have duplicate entries
    * 3- No element of table is Nil()
    * 4- Each element of data has to be present in table
    */
    def algorithmProperties[T](data: List[T], table: List[List[T]]): Boolean = {
        table.nonEmpty &&
        isUnique(table) &&
        table.forall(tableElement => tableElement.nonEmpty) &&
        data.forall(dataElement => table.contains(List[T](dataElement)))
    }

    def isValidIndex[T](index: BigInt, table: List[T]): Boolean = {
        index >= 0 && index < table.size
    }

    def appendProperty[T](left: List[T], right: List[T]): Boolean = (right match {
        case Nil() => true
        case Cons(x, xs) => ((left :+ x) ++ xs) == (left ++ right) because {
          snocIsAppend(left, x) && appendAssoc(left, List[T](x), xs)
        }
    }).holds

    def prependProperty[T](element: T, list: List[T]): Boolean = {
        element :: list == List[T](element) ++ list && appendProperty(List[T](element), list)
    }

    def compressedDataProperties(cmpData: List[BigInt], table: List[List[Bit]]): Boolean = {
        def validHeadIndex(list: List[BigInt]): Boolean = {
            list.nonEmpty && isValidIndex(list.head, table)
        }

        cmpData.isEmpty || validHeadIndex(cmpData)
    }

    /** Proves that 'findApplyCycle' holds
      * for lists without duplicate elements
      */
    def uniqueProperty[T](index: BigInt, element: T, list: List[T]): Boolean = {
        require(uniqueConditions(index, element, list))
        findApplyCycle(index, element, list)
    }.holds

    def findApplyCycle[T](index: BigInt, element: T, list: List[T]): Boolean = {
        require(isValidIndex(index, list))
        list.indexOf(element) == index &&
        list(index) == element
    }

    def isUnique[T](list: List[T]): Boolean = {
        list == list.unique
    }
    
    def uniqueConditions[T](index: BigInt, element: T, list: List[T]): Boolean = {
        isValidIndex(index, list) && isUnique(list) && (list.indexOf(element) == index || list(index) == element)
    }
}
