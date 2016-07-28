import leon.lang._
import leon.collection._
import leon.annotation._

object HashTables {

  @extern
  def hashingWrapper(x: BigInt, length: Int)(hashFun: (BigInt) => Int): Int = {
    hashFun(x) % length
  } ensuring(res => res >= 0 && res < length)
    

  case class HashTable(table: Array[List[BigInt]], hashFun: (BigInt) => Int, var content: Set[BigInt]) {
    require(table.length > 0 && table.length < 6 &&
            forall((i:Int, x: BigInt) => 
              ((0 <= i && i < table.length && table(i).content.contains(x)) ==> (hashing(x) == i))) &&
            forall((x: BigInt) => content.contains(x) ==> table(hashing(x)).content.contains(x))
    )

    //def content: Set[BigInt] = {
    //  def rec(index: Int): Set[BigInt] = {
    //    require(index >= 0 && index <= table.length)
    //    if(index == table.length) Set() else table(index).content ++ rec(index+1)
    //  }
    //  rec(0)
    //}

    def hashing(x: BigInt): Int = hashingWrapper(x, table.length)(hashFun)

    def apply(index: Int): List[BigInt] = {
      require(index >= 0 && index < table.length)
      table(index)
    }

    def insert(x: BigInt): Unit = {
      val index = hashing(x)
      table(index) = (x::table(index))
      content += x
    } ensuring(_ => table(hashing(x)).contains(x) && this.content == old(this).content ++ Set(x))

    def contains(x: BigInt): Boolean = {
      val index = hashing(x)
      table(index).contains(x)
    } ensuring(res => res == this.content.contains(x))
  }

  def test(ht: HashTable): Boolean = {
    ht.insert(4)
    ht.insert(6)
    ht.insert(7)
    ht.insert(5)
    ht.contains(4)
  } ensuring(res => res)

  def testHarness(ht: HashTable, x1: BigInt, x2: BigInt, x3: BigInt): Boolean = {
    ht.insert(x1)
    ht.insert(x2)
    ht.insert(x3)
    ht.contains(x1) && ht.contains(x2) && ht.contains(x3)
  } holds


  //case class HashTableMap(table: Array[List[BigInt]], hashFun: (BigInt) => Int) {
  //  def content: Map[BigInt, Int]
}
