package cp

object Serialization {
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

  case class Serialized(string : String, id : Int)

  def serialize(obj : Any) : Serialized = {
    val bos = new ByteArrayOutputStream()
    val oos = new ObjectOutputStream(bos)

    oos.writeObject(obj)
    oos.flush()
    bos.close()

    val array = bos.toByteArray
    val string = new String(array, encoding)

    Serialized(string, UniqueCounter.next)
  }

  def deserialize[A](serialized : Serialized) : A = {
    val Serialized(string, id) = serialized
    cache.get(id) match {
      case Some(cached) =>
        cached.asInstanceOf[A]
      case None =>
        val bis = new ByteArrayInputStream(string.getBytes(encoding))
        val ois = new ObjectInputStream(bis)

        val recovered : A = ois.readObject().asInstanceOf[A]
        bis.close()
        
        cache += (id -> recovered)
        recovered
    }
  }

  def getProgram(serialized : Serialized) : Program =
    deserialize[Program](serialized)

  def getInputVarList(serialized : Serialized) : List[Variable] =
    deserialize[List[Variable]](serialized)
}
