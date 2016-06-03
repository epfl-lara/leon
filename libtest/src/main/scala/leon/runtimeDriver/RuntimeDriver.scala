package leon

import annotation._
import lang._
import collection._
import scala.collection.immutable.{List => scalaList}
import scala.collection.mutable.{ListBuffer => scalaListBuffer}
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

	def plot(testSize: scalaList[BigInt], ops: List[()=>BigInt], orb: List[() => BigInt], function: String, orbOrInst: String) {

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

	def prettyprint(model: scalaListBuffer[BigInt], id: List[String]): String = {
		var j = 0
		var s = ""
		if(model.size == 1) {
			s = model(0) + s
			return s
		} else {
			s = s"${model(0)}"
			s = " + " + s
			j = 1
			while(j != model.size - 1) {
				s = s"${model(j)}*${id(j)}" + s
				s = " + " + s
				j = j + 1
			}
			s = s"${model(model.size - 1)}*${id(model.size - 1)}" + s
			return s
		}
	}

	def goesThrough(ops: List[BigInt], model: scalaListBuffer[BigInt], subsval: List[scalaListBuffer[BigInt]]): (Boolean, Int)  = {
		var j = 0
		while(j != ops.size) {
			var x = ops(j)
			var i = 0
			var y = model(0)
			i = 1
			while(i != model.size) {
				y = y + model(i)*subsval(i - 1)(j)
				i = i + 1
			}
			if(x > y) return (false, j)
			j = j + 1
		}
		return (true, 0)
	}

	def minreport(ops: List[BigInt], model: scalaListBuffer[BigInt], subsval: List[scalaListBuffer[BigInt]], points: scalaListBuffer[BigInt], here: Int): (scalaListBuffer[BigInt], BigInt) = {
		var tempmodel = model.clone()
		tempmodel(here) = tempmodel(here) - 1 
		var res = (model, points(0))
		var flag = false
		while(!flag) {
			val gt = goesThrough(ops, tempmodel, subsval)
			if(gt._1) {
				print(s"tempmodel before update $tempmodel\n")
				tempmodel(here) = tempmodel(here) - 1 
				print(s"tempmodel after update $tempmodel\n")
			} else {
				res = (tempmodel, points(gt._2))
				flag = true
			}
		}
		return res
	}

	def minresults(ops: List[BigInt], model: scalaListBuffer[BigInt], id: List[String], subsval: List[scalaListBuffer[BigInt]], points: scalaListBuffer[BigInt], filename: String) {
		require((model.size == points.size + 1) && (model.size == id.size))
		var j = 0
		val restream = new FileWriter(s"results/MINRESULTS${filename}.report")
    	val resout = new BufferedWriter(restream)
		resout.write(s"Orb infereed formula: ${prettyprint(model, id)}\n\n")
		while(j != model.size) {
			var (x, y) = minreport(ops, model, subsval, points, j)
			var newmodel = x.clone()
			newmodel(j) = newmodel(j) + 1
			
			print(s"x is $x")
			print(s"newmodel is $newmodel")

			resout.write(s"Least value of coeff ${j} is ${newmodel(j)}.\nThe formula that goes through is ${prettyprint(newmodel, id)}.\n")
			resout.write(s"Counter-example for ${prettyprint(x, id)} is at the point ${y}\n\n")
			j = j + 1
		}
		resout.write(s"Minimization report ends here\n\n")
		resout.close()
	}

}
