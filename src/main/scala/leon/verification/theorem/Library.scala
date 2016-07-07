
package leon
package verification
package theorem

import purescala.Definitions._

case class Library(program: Program) {
  
  lazy val Theorem = lookup("leon.theorem.Theorem").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Identifier = lookup("leon.theorem.Identifier").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Term = lookup("leon.theorem.Term").collectFirst { case acd : AbstractClassDef => acd }

  lazy val Variable = lookup("leon.theorem.Variable").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Application = lookup("leon.theorem.Application").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val BooleanLiteral = lookup("leon.theorem.BooleanLiteral").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val CharLiteral = lookup("leon.theorem.CharLiteral").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val StringLiteral = lookup("leon.theorem.StringLiteral").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val IntLiteral = lookup("leon.theorem.IntLiteral").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val BigIntLiteral = lookup("leon.theorem.BigIntLiteral").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val And = lookup("leon.theorem.And").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Or = lookup("leon.theorem.Or").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Implies = lookup("leon.theorem.Implies").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Iff = lookup("leon.theorem.Iff").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Not = lookup("leon.theorem.Not").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Forall = lookup("leon.theorem.Forall").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Exists = lookup("leon.theorem.Exists").collectFirst { case ccd : CaseClassDef => ccd }
  lazy val Equals = lookup("leon.theorem.Equals").collectFirst { case ccd : CaseClassDef => ccd }

  def lookup(name: String): Seq[Definition] = {
    program.lookupAll(name)
  }
}