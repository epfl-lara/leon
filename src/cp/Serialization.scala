package cp

trait Serialization {
  import java.io.{ByteArrayInputStream,ByteArrayOutputStream,ObjectInputStream,ObjectOutputStream}
  import purescala.Definitions._
  import purescala.Trees._
  import purescala.Common.Identifier

  private val cache = new scala.collection.mutable.HashMap[Int,Any]()
  private val encoding = "Latin1"

  private object UniqueCounter {
    private var soFar: Int = -1

    def next: Int = {
      soFar = soFar + 1
      soFar
    }
  }

  def serialize(obj : Any) : (String, Int) = {
    val bos = new ByteArrayOutputStream()
    val oos = new ObjectOutputStream(bos)

    oos.writeObject(obj)
    oos.flush()
    bos.close()

    val array = bos.toByteArray
    val string = new String(array, encoding)

    (string, UniqueCounter.next)
  }

  def deserialize[A](serialized : String, id : Int) : A = cache.get(id) match {
    case Some(cached) =>
      cached.asInstanceOf[A]
    case None =>
      val bis = new ByteArrayInputStream(serialized.getBytes(encoding))
      val ois = new ObjectInputStream(bis)

      val recovered : A = ois.readObject().asInstanceOf[A]
      bis.close()
      
      cache += (id -> recovered)
      recovered
  }

  def getProgram(serialized : String, id : Int) : Program =
    deserialize[Program](serialized, id)

  def getInputVarList(serialized : String, id : Int) : List[Variable] =
    deserialize[List[Variable]](serialized, id)
}

object Serialization extends Serialization
