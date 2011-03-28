package cp

trait Serialization {
  import java.io.{FileInputStream,FileOutputStream,ObjectInputStream,ObjectOutputStream,File}
  import purescala.Definitions._
  import purescala.Trees._

  private val fileSuffix = ""
  private val dirName = "serialized"
  private val directory = new java.io.File(dirName)

  private var cachedProgram : Option[Program] = None
  private val exprMap = new scala.collection.mutable.HashMap[String,Expr]()

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
  def writeProgram(prog : Program) : String = {
    directory.mkdir()

    val file = new java.io.File(directory, programFileName(prog))
    file.delete()

    writeObject(file, prog)
  }

  def writeExpr(pred : Expr) : String = {
    directory.mkdir()

    val file = java.io.File.createTempFile("expr", fileSuffix, directory)
    
    writeObject(file, pred)
  }

  private def readObject[A](filename : String) : A = {
    val fis = new FileInputStream(filename)
    val ois = new ObjectInputStream(fis)

    val recovered : A = ois.readObject().asInstanceOf[A]
    fis.close()

    recovered
  }

  private def readProgram(filename : String) : Program = {
    readObject[Program](filename)
  }

  private def readExpr(filename : String) : Expr = {
    readObject[Expr](filename)
  }

  def getProgram(filename : String) : Program = cachedProgram match {
    case None => val r = readProgram(filename); cachedProgram = Some(r); r
    case Some(cp) => cp
  }

  def getExpr(filename : String) : Expr = exprMap.get(filename) match {
    case Some(p) => p
    case None => val p = readExpr(filename); exprMap += (filename -> p); p
  }
}

object Serialization extends Serialization
