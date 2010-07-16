//	piskac@larapc01:~/guru$ pwd
//	/home/piskac/guru
//	piskac@larapc01:~/guru$ scalac -d bin/ src/guru/multisets/*.scala
//	piskac@larapc01:~/guru$ scala -cp bin/ guru.multisets.Main

package multisets


object Multisets  {

  def main(args: Array[String]) : Unit = {
    if (args.length == 0) {
      println("Usage: scala -cp bin/ guru.multisets.Main fileName ")
    } else {
      val fileName = args(0)
      multisets.MAPARun.run(fileName)
    }
  }
}

