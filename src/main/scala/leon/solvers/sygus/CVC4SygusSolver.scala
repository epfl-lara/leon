/* Copyright 2009-2015 EPFL, Lausanne */

package leon
package solvers
package sygus

import purescala._
import Definitions.Program

import synthesis.Problem

import smtlib._

class CVC4SygusSolver(ctx: LeonContext, pgm: Program, p: Problem) extends SygusSolver(ctx, pgm, p) with SMTLIBCVC4Target {

}
