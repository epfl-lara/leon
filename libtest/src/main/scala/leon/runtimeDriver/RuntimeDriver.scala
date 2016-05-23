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
	def generatePlotFile(function: String):String = {
s"""set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for Orb vs Runnable code, ${function}"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/orbVsActual${function}10.jpg"
plot \\
"<(sed -n '1,20p' results/orb${function}.data)" using 1:2 t'orb' with linespoints, \\
"<(sed -n '1,20p' results/ops${function}.data)" using 1:2 t'oper' with linespoints, 

set output "results/orbVsActual${function}100.jpg"
plot \\
"<(sed -n '20,40p' results/orb${function}.data)" using 1:2 t'orb' with linespoints, \\
"<(sed -n '20,40p' results/ops${function}.data)" using 1:2 t'oper' with linespoints,

set output "results/orbVsActual${function}1000.jpg"
plot \\
"<(sed -n '40,50p' results/orb${function}.data)" using 1:2 t'orb' with linespoints, \\
"<(sed -n '40,50p' results/ops${function}.data)" using 1:2 t'oper' with linespoints, 
"""
	}

	def run(testSize: scalaList[BigInt], ops: List[() => BigInt], orb: List[() => BigInt], function: String) {

		val orbstream = new FileWriter(s"results/orb${function}.data")
    val orbout = new BufferedWriter(orbstream)
		var j = 0
		for(i <- testSize) {
		  orbout.write(s"$i ${orb(j)()}\n")
		  j = j + 1
		}
    orbout.close()

    val opsstream = new FileWriter(s"results/ops${function}.data")
    val opsout = new BufferedWriter(opsstream)
    j = 0
		for(i <- testSize) {
		  opsout.write(s"$i ${ops(j)()}\n")
		  j = j + 1
		}
		opsout.close()

		val plotstream = new FileWriter(s"results/plot${function}.gnu")
    val plotout = new BufferedWriter(plotstream)
	  plotout.write(generatePlotFile(function))
		plotout.close()

		val result = s"gnuplot results/plot${function}.gnu" !!
	}	
}
