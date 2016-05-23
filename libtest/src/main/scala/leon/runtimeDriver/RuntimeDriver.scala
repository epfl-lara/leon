package leon

import annotation._
import lang._
import collection._
import scala.collection.immutable.{List => scalaList}
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation
import scala.sys.process._

import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter

package object runtimeDriver {
	def run(testSize: scalaList[BigInt], ops: List[() => BigInt], orb: List[() => BigInt]) {

		val orbstream = new FileWriter("results/orb.data")
    val orbout = new BufferedWriter(orbstream)
		var j = 0
		for(i <- testSize) {
		  orbout.write(s"$i ${orb(j)()}\n")
		  j = j + 1
		}
    orbout.close()

    val opsstream = new FileWriter("results/ops.data")
    val opsout = new BufferedWriter(opsstream)
    j = 0
		for(i <- testSize) {
		  opsout.write(s"$i ${ops(j)()}\n")
		  j = j + 1
		}
		opsout.close()

		val result = "gnuplot results/plot.gnu" !!
	}	
}
