package cp

trait Serialization {
  import java.io.{FileInputStream,FileOutputStream,ObjectInputStream,ObjectOutputStream,File}
  import purescala.Definitions._
  import purescala.Trees._

  private val filePrefix = "serialized"
  private val fileSuffix = ""
  private val dirName = "serialized"
  private val directory = new java.io.File(dirName)

  private var cachedProgram : Option[Program] = None
  private val exprMap = new scala.collection.mutable.HashMap[String,Expr]()
  private val outputVarListMap = new scala.collection.mutable.HashMap[String,List[String]]()
  private val inputVarListMap  = new scala.collection.mutable.HashMap[String,List[Variable]]()

  def programFileName(prog : Program) : String = {
    prog.mainObject.id.toString + fileSuffix
  }

  private def writeObject(file : File, obj : Any) : String = {
    val fos = new FileOutputStream(file)
    val oos = new ObjectOutputStream(fos)

    oos.writeObject(obj)
    oos.flush()
    fos.close()

    file.getAbsolutePath()

  }

  def writeObject(obj : Any) : String = {
    directory.mkdir()

    val file = java.io.File.createTempFile(filePrefix, fileSuffix, directory)
    
    writeObject(file, obj)
  }

  private def readObject[A](filename : String) : A = {
    val fis = new FileInputStream(filename)
    val ois = new ObjectInputStream(fis)

    val recovered : A = ois.readObject().asInstanceOf[A]
    fis.close()

    recovered
  }

  def getProgram(filename : String) : Program = cachedProgram match {
    case Some(cp) => cp
    case None => val r = readObject[Program](filename); cachedProgram = Some(r); r
  }

  def getExpr(filename : String) : Expr = exprMap.get(filename) match {
    case Some(e) => e
    case None => val e = readObject[Expr](filename); exprMap += (filename -> e); e
  }

  def getOutputVarList(filename : String) : List[String] = outputVarListMap.get(filename) match {
    case Some(l) => l
    case None => val l = readObject[List[String]](filename); outputVarListMap += (filename -> l); l
  }

  def getInputVarList(filename : String) : List[Variable] = inputVarListMap.get(filename) match {
    case Some(l) => l
    case None => val l = readObject[List[Variable]](filename); inputVarListMap += (filename -> l); l
  }
}

object Serialization extends Serialization
