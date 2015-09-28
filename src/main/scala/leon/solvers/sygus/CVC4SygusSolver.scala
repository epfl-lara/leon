/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package sygus

import purescala._
import Definitions.Program

import synthesis.Problem

import leon.solvers.smtlib._

import _root_.smtlib.interpreters.CVC4Interpreter

class CVC4SygusSolver(ctx: LeonContext, pgm: Program, p: Problem) extends SygusSolver(ctx, pgm, p) with SMTLIBCVC4QuantifiedTarget {
  override def targetName = "cvc4-sygus";

  def interpreterOps(ctx: LeonContext) = {
    Seq(
      "-q",
      "--cegqi-si",
      "--cbqi-sym-lia",
      "--macros-quant",
      "--lang", "sygus",
      "--print-success"
    )
  }

  protected val allowQuantifiedAssertions: Boolean = true
}
