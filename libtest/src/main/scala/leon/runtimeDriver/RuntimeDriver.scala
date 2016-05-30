package leon

import annotation._
import lang._
import collection._
import scala.collection.immutable.{List => scalaList}
import scala.language.implicitConversions
import scala.annotation.StaticAnnotation
import scala.sys.process._
import scala.math._

import java.io.File
import java.io.FileWriter
import java.io.BufferedWriter

package object runtimeDriver {
	def generatePlotFile(function: String, orbOrInst: String):String = {
s"""set terminal jpeg

set key left top

set xlabel "n"
set ylabel "time"
set title "Plot for ${orbOrInst} vs Runnable code, size ${function}"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/${orbOrInst}VsActual${function}10.jpg"
plot \\
"<(sed -n '1,20p' results/${orbOrInst}${function}.data)" using 1:2 t'${orbOrInst}' with linespoints, \\
"<(sed -n '1,20p' results/ops${function}.data)" using 1:2 t'oper' with linespoints, 

set output "results/${orbOrInst}VsActual${function}100.jpg"
plot \\
"<(sed -n '20,40p' results/${orbOrInst}${function}.data)" using 1:2 t'${orbOrInst}' with linespoints, \\
"<(sed -n '20,40p' results/ops${function}.data)" using 1:2 t'oper' with linespoints,

set output "results/${orbOrInst}VsActual${function}1000.jpg"
plot \\
"<(sed -n '40,50p' results/${orbOrInst}${function}.data)" using 1:2 t'${orbOrInst}' with linespoints, \\
"<(sed -n '40,50p' results/ops${function}.data)" using 1:2 t'oper' with linespoints, 
"""
	}

	def generateLogPlotFile(function: String, size: Int, orbOrInst: String):String = {
s"""set terminal jpeg

set key left top

set xlabel "log(n)"
set ylabel "time"
set title "Plot for ${orbOrInst} vs Runnable code, log size vs ${function}"

set grid ytics lt 0 lw 1 lc rgb "#bbbbbb"
set grid xtics lt 0 lw 1 lc rgb "#bbbbbb"

set output "results/${orbOrInst}VsActual${function}.jpg"
plot \\
"<(sed -n '1,${size}p' results/${orbOrInst}${function}.data)" using 1:2 t'${orbOrInst}' with linespoints, \\
"<(sed -n '1,${size}p' results/ops${function}.data)" using 1:2 t'oper' with linespoints, 
"""
	}

	def plot(testSize: scalaList[BigInt], ops: List[() => BigInt], orb: List[() => BigInt], function: String, orbOrInst: String) {

	val orbstream = new FileWriter(s"results/${orbOrInst}${function}.data")
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
	  plotout.write(generatePlotFile(function, orbOrInst))
		plotout.close()

		val result = s"gnuplot results/plot${function}.gnu" !!
	}	

	def logplot(testSize: scalaList[Int], ops: List[() => BigInt], orb: List[() => BigInt], function: String, orbOrInst: String) {

	val orbstream = new FileWriter(s"results/${orbOrInst}${function}.data")
    val orbout = new BufferedWriter(orbstream)
		var j = 0
		for(i <- testSize) {
		  orbout.write(s"${log(i.doubleValue)/log(2)} ${orb(j)()}\n")
		  j = j + 1
		}
    orbout.close()

    val opsstream = new FileWriter(s"results/ops${function}.data")
    val opsout = new BufferedWriter(opsstream)
    j = 0
		for(i <- testSize) {
		  opsout.write(s"${scala.math.log(i.doubleValue)/scala.math.log(2)} ${ops(j)()}\n")
		  j = j + 1
		}
		opsout.close()

		val plotstream = new FileWriter(s"results/plot${function}.gnu")
    val plotout = new BufferedWriter(plotstream)
	  plotout.write(generateLogPlotFile(function, testSize.size, orbOrInst))
		plotout.close()

		val result = s"gnuplot results/plot${function}.gnu" !!
	}

	def dumplogdata(testSize: scalaList[Int], ops: List[() => BigInt], orb: List[() => BigInt], function: String, orbOrInst: String) {

	val orbstream = new FileWriter(s"results/${orbOrInst}${function}.data")
    val orbout = new BufferedWriter(orbstream)
		var j = 0
		for(i <- testSize) {
		  orbout.write(s"${log(i.doubleValue)/log(2)} ${orb(j)()}\n")
		  j = j + 1
		}
    orbout.close()

    val opsstream = new FileWriter(s"results/ops${function}.data")
    val opsout = new BufferedWriter(opsstream)
    j = 0
		for(i <- testSize) {
		  opsout.write(s"${scala.math.log(i.doubleValue)/scala.math.log(2)} ${ops(j)()}\n")
		  j = j + 1
		}
		opsout.close()
	}
}
