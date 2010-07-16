package multisets

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator._
import scala.util.parsing.input._
import scala.util.parsing.syntax._
import scala.collection.mutable.Map
import java.io.FileReader


object MAPAParser extends StandardTokenParsers {

  lexical.delimiters ++= List( "(", ")", ",",  ".", ":", "=", "<", "_", "{", "}", "+", "|", "-", "*" );
  lexical.reserved ++= List( "Problem", "Variables", "Formula", "And", "Or", 
     "Implies", "Equiv", "Not", "true", "false", "SUB", "ALLe", "VEC", "ite", "e", 
      "empty", "INTR", "UN", "PLUS", "SETof", "SUM" );


  def inputFile: Parser[ List[(String, (Map[String, String], Formula))] ] = (
     rep(oneProblemInFile) 
    | failure( "Cannot parse the input file." ))


  def oneProblemInFile: Parser[(String, (Map[String, String], Formula))] = (
     ("Problem" ~> "(" ~>  ident <~ ",") ~ ("Variables" ~> "(" ~> myVars <~ ")" <~ ",") ~ ("Formula" ~> "(" ~> myFla <~ ")" <~ ")" <~ "." ) ^^ 
        { case name ~ vars ~ fla  =>  (name.toString, (vars, fla) ) }
    | failure( "Cannot parse this problem." ))


  def myVars: Parser[ Map[String, String] ] = (
    repsep(oneVar, ",") ^^ createMap
    | failure( "Cannot parse this Variables string." ))

  def oneVar: Parser[ (String, String) ] = (
    (ident ~ ":" ~ ident)^^ { case name ~ ":" ~ typeV  => (name.toString, typeV.toString ) }
    | failure( "Cannot parse this variable." ))

  def createMap(l: List[(String, String)]):  Map[String, String] = {
    val m = Map[String, String]()
    l.foreach(p => m += (p._1 -> p._2))
    m
  }


  def myFla: Parser[ Formula ]  = (
      myAtom ^^ (FAtom(_))
    | ("And" ~> "(" ~> myFla  <~ ",") ~ (myFla <~ ")")^^ {case f1 ~ f2 => FAnd(f1, f2)}
    | ("Or" ~> "(" ~> myFla <~ ",") ~ (myFla <~ ")")^^ {case f1 ~ f2 => FOr(f1, f2)}
    | ("Implies" ~> "(" ~> myFla <~ ",") ~ (myFla <~ ")")^^ {case f1 ~ f2 => FOr(FNot(f1), f2)}
    | ("Equiv" ~> "(" ~> myFla <~ ",") ~ (myFla <~ ")")^^ {case f1 ~ f2 => FOr(FAnd(f1, f2), FAnd(FNot(f1), FNot(f2)))}
    | ("Not" ~> "(" ~> myFla <~ ")") ^^ {case f1  => FNot(f1)}
    | "true" ^^ (f => FTrue)
    | "false" ^^ (f => FFalse)
    | failure( "Cannot parse this Formula string." ))


  def myAtom: Parser[ Atom ]  = (
      myAtomOut ^^ (AAtomOut(_))
    | ("=" ~> "(" ~> myMset <~ ",") ~ (myMset <~ ")")^^ { case m1 ~ m2  => AEqual(m1, m2) }
    | ("SUB" ~> "(" ~> myMset <~ ",") ~ (myMset <~ ")")^^ { case m1 ~ m2  => ASubset(m1, m2) }
    | ("ALLe" ~> "." ~> myFlaIn)^^ { case f1   => AForAllElem(f1) }
    | failure( "Cannot parse this atom." ))


  def myFlaOut: Parser[ FormulaOut ]  = (
      myAtomOut ^^ (FOAtom(_))
    | ("And" ~> "(" ~> myFlaOut  <~ ",") ~ (myFlaOut <~ ")")^^ {case f1 ~ f2 => FOAnd(f1, f2)}
    | ("Or" ~> "(" ~> myFlaOut <~ ",") ~ (myFlaOut <~ ")")^^ {case f1 ~ f2 => FOOr(f1, f2)}
    | ("Implies" ~> "(" ~> myFlaOut <~ ",") ~ (myFlaOut <~ ")")^^ {case f1 ~ f2 => FOOr(FONot(f1), f2)}
    | ("Equiv" ~> "(" ~> myFlaOut <~ ",") ~ (myFlaOut <~ ")")^^ {case f1 ~ f2 => FOOr(FOAnd(f1, f2), FOAnd(FONot(f1), FONot(f2)))}
    | ("Not" ~> "(" ~> myFlaOut <~ ")") ^^ {case f1  => FONot(f1)}
    | "true" ^^ (f => FOTrue)
    | "false" ^^ (f => FOFalse)
    | failure( "Cannot parse this formula." ))


  def myAtomOut: Parser[ AtomOut ]  = (
      ("=" ~> "(" ~> myTrmOut <~ ",") ~ (myTrmOut <~ ")")^^ { case i1 ~ i2  => AOEq(i1, i2) }
    | ("<" ~> "=" ~> "(" ~> myTrmOut <~ ",") ~ (myTrmOut <~ ")")^^ { case i1 ~ i2  => AOLeq(i1, i2) }
    | ("=" ~> "(" ~> "VEC" ~> "(" ~> myListTrmOut <~ ")" <~"," ) ~ ("SUM" ~> "_" ~> "{" ~> myFlaIn <~ "}") ~ 
        ("VEC" ~> "(" ~> myListTrmIn <~ ")" <~ ")") ^^ { case l1 ~ f ~ l2   => AOSum(l1, f, l2) }
    | failure( "Cannot parse this atom." ))


  def  myListTrmOut: Parser[ List[TermOut] ]  = (
      repsep(myTrmOut, ",") 
    | failure( "Cannot parse this vector." ))


  def myTrmOut: Parser[ TermOut ]  = (
      myInt ^^ {case n  =>  TOConstant(n) }
    | ident ^^ {case s =>  TOVariable(s.toString) }
    | ("*" ~> "(" ~> myInt <~ ",") ~ (myTrmOut <~ ")") ^^ {case n ~ t => TOTimes(n, t) }
    | ("|" ~> myMset <~ "|") ^^ { case m => TOCard(m) }
    | ("+" ~> "(" ~> myListTrmOut <~ ")") ^^  createSumOfOutterTerms
    | ("ite" ~> "(" ~> myFlaOut <~ ",") ~ myTrmOut ~ ("," ~> myTrmOut <~ ")")   ^^ { case f ~ t1 ~ t2 => TOIte(f, t1, t2) }
    | failure( "Cannot parse this term." ))


  def createSumOfOutterTerms(l: List[TermOut]):  TermOut = {
    if (l.isEmpty) TOConstant(0) else {
      var t = l.head
      val l1 = l.tail
      l1.foreach(e => t = TOPlus(t, e))
      t
    }
  }


  def myFlaIn: Parser[ FormulaIn ]  = (
      myAtomIn ^^ (FIAtom(_))
    | ("And" ~> "(" ~> myFlaIn  <~ ",") ~ (myFlaIn <~ ")")^^ {case f1 ~ f2 => FIAnd(f1, f2)}
    | ("Or" ~> "(" ~> myFlaIn <~ ",") ~ (myFlaIn <~ ")")^^ {case f1 ~ f2 => FIOr(f1, f2)}
    | ("Implies" ~> "(" ~> myFlaIn <~ ",") ~ (myFlaIn <~ ")")^^ {case f1 ~ f2 => FIOr(FINot(f1), f2)}
    | ("Equiv" ~> "(" ~> myFlaIn <~ ",") ~ (myFlaIn <~ ")")^^ {case f1 ~ f2 => FIOr(FIAnd(f1, f2), FIAnd(FINot(f1), FINot(f2)))}
    | ("Not" ~> "(" ~> myFlaIn <~ ")") ^^ {case f1  => FINot(f1)}
    | "true" ^^ (f => FITrue)
    | "false" ^^ (f => FIFalse)
    | failure( "Cannot parse this formula." ))


  def myAtomIn: Parser[ AtomIn ]  = (
      ("=" ~> "(" ~> myTrmIn <~ ",") ~ (myTrmIn <~ ")") ^^ { case i1 ~ i2  => AIEq(i1, i2) }
    | ("<" ~> "=" ~> "(" ~> myTrmIn <~ ",") ~ (myTrmIn <~ ")") ^^ { case i1 ~ i2  => AILeq(i1, i2) }
    | failure( "Cannot parse this atom." ))


  def myListTrmIn: Parser[ List[TermIn] ]  = (
      repsep(myTrmIn, ",") 
    | failure( "Cannot parse this vector." ))


  def myTrmIn: Parser[ TermIn ]  = (
      myInt ^^ {case n  =>  TIConstant(n) }
    | (ident <~ "(" <~ "e" <~ ")") ^^ { case s => TIMultiplicity(s.toString) }
    | ("*" ~> "(" ~> myInt <~ ",") ~ (myTrmIn <~ ")") ^^ {case n ~ t => TITimes(n, t) }
    | ("+" ~> "(" ~> myListTrmIn <~ ")") ^^  createSumOfInnerTerms
    | ("ite" ~> "(" ~> myFlaIn <~ ",") ~ myTrmIn ~ ("," ~> myTrmIn <~ ")")   ^^ { case f ~ t1 ~ t2 => TIIte(f, t1, t2) }
    | failure( "Cannot parse this term." ))

  def createSumOfInnerTerms(l: List[TermIn]):  TermIn = {
    if (l.isEmpty) TIConstant(0) else {
      var t = l.head
      val l1 = l.tail
      l1.foreach(e => t = TIPlus(t, e))
      t
    }
  }


 def myInt: Parser[ Int ] = (
    "-" ~> numericLit ^^ (x => x.toInt * -1)
  | numericLit ^^ ( x => x.toInt )
  | failure( "Cannot parse this number." ))


  def myMset: Parser[ Multiset ]  = (
      ident ^^ { case s => MVariable(s.toString) }
    | "empty" ^^ { x => MEmpty}
    | ("INTR" ~> "(" ~> myListMset <~ ")") ^^  createIntersectionOfMSets
    | ("UN" ~> "(" ~> myListMset <~ ")") ^^  createUnionOfMSets
    | ("PLUS" ~> "(" ~> myListMset <~ ")") ^^  createSumOfMSets
    | ("-" ~> "(" ~> myMset <~ ",") ~ (myMset <~ ")") ^^ {case m1 ~ m2 => MMinus(m1, m2) }
    | ("-" ~> "-" ~> "(" ~> myMset <~ ",") ~ (myMset <~ ")") ^^ {case m1 ~ m2 => MSetMinus(m1, m2) }
    | ("SETof" ~> "(" ~> myMset <~ ")") ^^ {case m =>  MSetOf(m) }
    | failure( "Cannot parse this multiset." ))

  def createIntersectionOfMSets(l: List[Multiset]):  Multiset = {
    if (l.isEmpty) MEmpty else {
      var t = l.head
      val l1 = l.tail
      l1.foreach(e => t = MIntersection(t, e))
      t
    }
  }

  def createUnionOfMSets(l: List[Multiset]):  Multiset = {
    if (l.isEmpty) MEmpty else {
      var t = l.head
      val l1 = l.tail
      l1.foreach(e => t = MUnion(t, e))
      t
    }
  }

  def createSumOfMSets(l: List[Multiset]):  Multiset = {
    if (l.isEmpty) MEmpty else {
      var t = l.head
      val l1 = l.tail
      l1.foreach(e => t = MPlus(t, e))
      t
    }
  }


  def myListMset: Parser[ List[Multiset] ]  = (
      repsep(myMset, ",") 
    | failure( "Cannot parse this vector." ))



//------------------------------------------------

 def main(fileName: String) : List[(String, (Map[String, String], Formula))] = {
  val reader = StreamReader(new FileReader(fileName))
  val tokens = new lexical.Scanner(reader)
  phrase(inputFile)(tokens) match {
    case Success( mapping, _ ) =>  mapping
    case e => throw(new Exception("Error = " + e))
  }
  }
}

