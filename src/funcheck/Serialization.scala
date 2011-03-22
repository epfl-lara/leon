package funcheck

import java.io.{FileInputStream,FileOutputStream,ObjectInputStream,ObjectOutputStream}
import purescala.Definitions.Program

trait Serialization {
  val fileSuffix = ".serialized"
  val dirName = "serialized"

  def programFileName(prog : Program) : String = {
    prog.mainObject.id.toString
  }

  def writeProgram(prog : Program) : String = {
    val directory = new java.io.File(dirName)
    directory.mkdir()

    val file = java.io.File.createTempFile(programFileName(prog), fileSuffix, directory)

    val fos = new FileOutputStream(file)
    val oos = new ObjectOutputStream(fos)

    oos.writeObject(prog)
    oos.flush()
    fos.close()

    file.getAbsolutePath()
  }

  def readProgram(filename : String) : Program = {
    val fis = new FileInputStream(filename)
    val ois = new ObjectInputStream(fis)

    val recovered : Program = ois.readObject().asInstanceOf[Program]
    fis.close()

    recovered
  }
}
