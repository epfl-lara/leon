package util

import org.scalatest.FunSuite
import org.scalatest.matchers.ShouldMatchers._

import java.io.{BufferedWriter, FileWriter, File}

import leon._
import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TreeOps._
import leon.solvers.z3._
import leon.solvers.Solver
import leon.synthesis._
import leon.synthesis.utils._

object Utils {

  def getFunDefByName(program: Program, name: String) = {
    assert(program.definedFunctions.exists({
      funDef: FunDef => funDef.id.name == name
    }),	"Function " + name + " not found. All functions: " + program.definedFunctions.map(_.id.name).mkString(", "))
    
    program.definedFunctions.find({
      funDef: FunDef => funDef.id.name == name
    }) match {
      case Some(res) => res
      case _ => null
    }
  }
  
}