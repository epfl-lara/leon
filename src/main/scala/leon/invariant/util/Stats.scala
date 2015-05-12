package leon
package invariant.util

import purescala.Common._
import purescala.Definitions._
import purescala.Expressions._
import purescala.ExprOps._
import purescala.Extractors._
import purescala.Types._
import scala.collection.mutable.{ Map => MutableMap }
import java.io._
import leon.invariant._
import java.io._
import scala.collection.mutable.{Map => MutableMap}


/**
 * A generic statistics object that provides:
 * (a) Temporal variables that change over time. We track the total sum and max of the values the variable takes over time
 * (b) Counters that are incremented over time. Variables can be associated with counters.
 *     We track the averages value of a variable over time w.r.t to the counters with which it is associated.
 */
object Stats {
  val keystats = MutableMap[String, (Long, Long)]()
  val counterMap = MutableMap[String, Seq[String]]()
  var cumKeys = Seq[String]()
  var timekeys = Set[String]() //this may be inner, outer or cumkey

  private def updateStats(newval: Long, key: String, cname: Option[String]) = {
    val (cum, max) = keystats.getOrElse(key, {
      val init = (0: Long, 0: Long)
      keystats += (key -> (0, 0))

      if (cname.isDefined) {
        val presentKeys = counterMap(cname.get)
        counterMap.update(cname.get, presentKeys :+ key)
      } else {
        cumKeys :+= key
      }
      init
    })
    val newcum = cum + newval
    val newmax = if (max < newval) newval else max
    keystats.update(key, (newcum, newmax))
  }
  //a special method for adding times
  private def updateTimeStats(newval: Long, key: String, cname: Option[String]) = {
    if (!timekeys.contains(key))
      timekeys += key
    updateStats(newval, key, cname)
  }

  def updateCumStats(newval: Long, key: String) = updateStats(newval, key, None)
  def updateCumTime(newval: Long, key: String) = updateTimeStats(newval, key, None)
  def updateCounter(incr: Long, key: String) = {
    if (!counterMap.contains(key)) {
      counterMap.update(key, Seq())
    }
    //counters are considered as cumulative stats
    updateStats(incr, key, None)
  }
  def updateCounterStats(newval: Long, key: String, cname: String) = updateStats(newval, key, Some(cname))
  def updateCounterTime(newval: Long, key: String, cname: String) = updateTimeStats(newval, key, Some(cname))

  private def getCum(key: String): Long = keystats(key)._1
  private def getMax(key: String): Long = keystats(key)._2

  def dumpStats(pr: PrintWriter) = {
    //Print cumulative stats
    cumKeys.foreach(key => {
      if (timekeys.contains(key)) {
        pr.println(key + ": " + (getCum(key).toDouble / 1000.0) + "s")
      } else
        pr.println(key + ": " + getCum(key))
    })

    //dump the averages and maximum of all stats associated with counters
    counterMap.keys.foreach((ckey) => {
      pr.println("### Statistics for counter: " + ckey + " ####")
      val counterval = getCum(ckey)
      val assocKeys = counterMap(ckey)
      assocKeys.foreach((key) => {
        if (timekeys.contains(key)) {
          pr.println("Avg." + key + ": " + (getCum(key).toDouble / (counterval * 1000.0)) + "s")
          pr.println("Max." + key + ": " + (getMax(key).toDouble / 1000.0) + "s")
        } else {
          pr.println("Avg." + key + ": " + (getCum(key).toDouble / counterval))
          pr.println("Max." + key + ": " + getMax(key))
        }
      })
    })
  }
}

/**
 * Statistics specific for this application
 */
object SpecificStats {

  var output: String = ""
  def addOutput(out: String) = {
    output += out + "\n"
  }
  def dumpOutputs(pr: PrintWriter) {
    pr.println("########## Outputs ############")
    pr.println(output)
    pr.flush()
  }

  //minimization stats
  var lowerBounds = Map[FunDef, Map[Variable, FractionalLiteral]]()
  var lowerBoundsOutput = Map[FunDef, String]()
  def addLowerBoundStats(fd: FunDef, lbMap: Map[Variable, FractionalLiteral], out: String) = {
    lowerBounds += (fd -> lbMap)
    lowerBoundsOutput += (fd -> out)
  }
  def dumpMinimizationStats(pr: PrintWriter) {
    pr.println("########## Lower Bounds ############")
    lowerBounds.foreach((pair) => {
      val (fd, lbMap) = pair
      pr.print(fd.id + ": \t")
      lbMap.foreach((entry) => {
        pr.print("(" + entry._1 + "->" + entry._2 + "), ")
      })
      pr.print("\t Test results: " + lowerBoundsOutput(fd))
      pr.println()
    })
    pr.flush()
  }
}