package leon.synthesis.comfusy
import scala.language.implicitConversions

object APASynthesisExamples {
  import APASynthesis._
  def O(name: String) = OutputVar(name)
  def I(name: String) = InputVar(name)
  implicit def OutputVarToPACombination(o: OutputVar):APACombination = APACombination(o)
  implicit def InputVarToPACombination(i: InputVar):APACombination = APACombination(i)
  implicit def IntegerToPACombination(k: Int):APAInputCombination = APAInputCombination(k)
  implicit def InputToPACombination(k: APAInputCombination):APACombination = APACombination(k)

  val x = O("x")
  val x1 = O("x1")
  val y = O("y")
  val y1 = O("y1")
  val z = O("z")

  val a = I("a")
  val b = I("b")
  val c = I("c")
  val d = I("d")
  
  APASynthesis.advanced_modulo = false
  APASynthesis.run_time_checks = true
  //APASynthesis.rendering_mode = RenderingPython
  APASynthesis.rendering_mode = RenderingScala
  Common.computing_mode = Common.OTBezout()

  def main(args : Array[String]) : Unit = {
    /*completeExample()
    hourMinutSecondExample()
    balancedProblem()
    dividesExample()
    rhymesExample()*/
    quotientExample()
    //multiplicativeInverseExample()
    //OptimizedExample()
    //extract7and8()
    //stepExample()
    //extractRatio()
    //multiArray()
    //APAExample()
    //paboucle()
  }
  
  def hourMinutSecondExample() {
    val seconds = I("seconds")
    val s = O("s")
    val m = O("m")
    val h = O("h")
    val condition = (
         seconds === s + (m * 60) + (h*3600)
      && s >= 0 && s < 60
      && m >= 0 && m < 60
    )
    val solution = APASynthesis.solve("getHourMinutSeconds", condition)
    println(solution._1)
    println(solution._2)
  }
  def balancedProblem() {
    val weight = I("weight")
    val w1 = O("w1")
    val w2 = O("w2")
    val w3 = O("w3")
    val c1 = APAEqualZero(APACombination(0, (-1, weight)::Nil, (1, w1)::(3, w2)::(9, w3)::Nil))
    val c2 = APAGreaterEqZero(APACombination(1, Nil, (1, w1)::Nil))
    val c3 = APAGreaterEqZero(APACombination(1, Nil, (-1, w1)::Nil))
    val c4 = APAGreaterEqZero(APACombination(1, Nil, (1, w2)::Nil))
    val c5 = APAGreaterEqZero(APACombination(1, Nil, (-1, w2)::Nil))
    val c6 = APAGreaterEqZero(APACombination(1, Nil, (1, w3)::Nil))
    val c7 = APAGreaterEqZero(APACombination(1, Nil, (-1, w3)::Nil))
    val solution = APASynthesis.solve("getWeights", c1::c2::c3::c4::c5::c6::c7::Nil)
    println(solution._1)
    println(solution._2)
  }
  
  def dividesExample() {
    val pac1 = APADivides(5, b+y)
    val pac2 = APADivides(7, c+y*b)
    val solution = APASynthesis.solve("divides5And7", pac1::pac2::Nil)
    println(solution._1)
    println(solution._2)
  }
  def completeExample() {
    val condition = ( y*c === b || y*b === c)
    val solution = APASynthesis.solve("solveEquation", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def stepExample() {
    val Nsyls = I("\\Nsyls")
    val Isyls = I("\\Isyls")
    val Elines     = I("\\Elines")
    val Ilines     = I("\\Ilines")
    val Tlines     = O("\\Tlines")
    val Nlines     = O("\\Nlines")
    val lines8     = O("\\lineeight")
    val lines7     = O("\\lineseven")
    val NSlines     = O("\\NSlines")
    
    val condition = (
           Nsyls + Isyls === lines8*8 + lines7*7
        && lines8 >= 0
        && lines7 >= 0
        && lines8 < 4*7
        && Tlines === Elines + Nlines
        && Nlines === lines8 + lines7
        && Nlines === Ilines + NSlines
        && (Tlines divisible_by 4)
    )
    
    val solution = APASynthesis.solve("rhymes78", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def rhymesExample() {
    /* Solves the following poem problem:
    We want to arrange names in a poem such that :
    -- Most verses are made of 8 syllables of names (ex: Denver Youcef Elisabeth)
    -- Maybe some are made of 7 syllables of names + 1 conjunction syllabe. (ex: Viktor Ruzica _and_ Philip)
    -- on verse rhymes with its predecessor or its successor.
    Aside from the rhyming problem, there is the arrangement problem.
    We have to know in advance how many lines of 7 and 8 syllables of names we will have, before filling them.
    
    Furthermore, the user supplies existing lines (such as the examples given above)
     * 
    */
    val complete_lines  = I("complete_lines")
    val incomplete_syllables = I("incomplete_syllables")
    val input_syllables      = I("input_syllables") /* Number of syllables to place */
    val incomplete_lines  = I("incomplete_lines")
    val new_lines         = O("new_lines")
    val new_empty_lines   = O("new_empty_lines")
    val total_lines       = O("total_lines")
    val lines_7_syllables  = O("lines_7_syllables")
    val lines_8_syllables  = O("lines_8_syllables")
    val condition = (
           total_lines === complete_lines    + new_lines
        && new_lines   === incomplete_lines  + new_empty_lines
        && new_lines   === lines_7_syllables + lines_8_syllables
        && incomplete_syllables + input_syllables === lines_7_syllables * 7 + lines_8_syllables * 8
        && (total_lines divisible_by 4)

        && lines_7_syllables >= 0
        && lines_8_syllables >= 0
        && total_lines >= 0
        && lines_7_syllables < 8*4      
    )
    val solution = APASynthesis.solve("rhymes78", condition)
    println(solution._1)
    println(solution._2)
  }

  def quotientExample() {
    //val b2 = b.assumeSign(1).toInputTerm
    //val condition = (a === (z*b2)*b2 + x*b2 + y && y >= 0 && y < b2 && x >= 0 && x < b2)
    //val condition = (a === x*b2 + y && y >= 0 && y < b2)
    val j = O("j")
    val k = O("k")
    val i = I("i")
    val x = I("x")
    val y = I("y")
    /*val condition = (i === k * x + j
    && j >= 0 && j < x
    && k >= 0&& k < y)*/
    val condition = APAConjunction(List(APAEqualZero(APACombination(APAInputCombination(0,
        List((1,InputVar("i")))),List((APAInputCombination(-1,List()),OutputVar("j")),
                                      (APAInputCombination(0,List((-1,InputVar("x")))),OutputVar("k"))))),
                                        APAGreaterEqZero(APACombination(APAInputCombination(0,List()),
        List((APAInputCombination(1,List()),OutputVar("j"))))),
        APAGreaterEqZero(APACombination(APAInputCombination(-1,List((1,InputVar("x")))),List((APAInputCombination(-1,List()),OutputVar("j"))))), APAGreaterEqZero(APACombination(APAInputCombination(0,List()),List((APAInputCombination(1,List()),OutputVar("k"))))), APAGreaterEqZero(APACombination(APAInputCombination(-1,List((1,InputVar("y")))),List((APAInputCombination(-1,List()),OutputVar("k")))))))
    
    println(condition)
    val solution = APASynthesis.solve("quotient", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def multiplicativeInverseExample() {
    val M = InputVar("M")
    val n = InputVar("n")
    val x = OutputVar("x")
    val condition = ((x*n - 1) divisible_by M.toInputTerm())
    val solution = APASynthesis.solve("multiplicativeInverse", condition)
    println(solution._1)
    println(solution._2)
  }
  
  /*def ArmandoExample() {
    return
    val N = InputVar("N").assumeSign(1)
    val P = InputVar("P").assumeSign(1)
    val p1 = InputVar("p1")
    val p2 = InputVar("p2")
    val e1 = OutputVar("e1")
    val s1 = OutputVar("s1")
    val e2 = OutputVar("e2")
    val s2 = OutputVar("s1")
    val p1len = OutputVar("p1len")
    val p2len = OutputVar("p2len")
    val rstart_c1 = OutputVar("rstart_c1")
    val rstart_c2 = OutputVar("rstart_c2")
    val rstart_c3 = OutputVar("rstart_c3")
    val rstart_c4 = OutputVar("rstart_c4")
    val rstart_c5 = OutputVar("rstart_c5")
    val rstart_c6 = OutputVar("rstart_c6")
    val rstart_c7 = OutputVar("rstart_c7")
    val rstart_c8 = OutputVar("rstart_c8")
    val rstart_c9 = OutputVar("rstart_c9")
    val condition = (
      ({val (proc, totProc, N) = (p1, P, N)
        val modNtoProc = APAInputMod(N.toInputTerm(), totProc.toInputTerm())
       (proc+rstart_c1 > modNtoProc +rstart_c2 && (proc-1+rstart_c3)*((N-1+rstart_c4)/totProc+rstart_c5-1)+modNtoProc+rstart_c6) ||
       (proc+rstart_c1 <= modNtoProc +rstart_c2 && (proc-1+rstart_c7)*((N-1+rstart_c8)/totProc+rstart_c9-1))
      }) &&
                     p1len === e1-s1 &&
                     p2len === e2-s2 &&
                     (p1len === p2len || p1len === p2len.toCombination() + 1 || p1len === p2len -1) &&
                     (p2 > p1+1 || p2 < p1+1 || s2===e1) &&
                     (p2 > p1-1 || p2 < p1-1 || e2===N) &&
                     (p1 > 0 || p1 < 0 || s1 === 0)
    )
    val solution = APASynthesis.solve("Armando", condition)
    println(solution._1)
    println(solution._2)
  }*/
  
  def OptimizedExample() {
    val condition = (x+y === a+b && (b < x && x < y || a < y && y < x))
    val solution = APASynthesis.solve("testnotdnf", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def extract7and8() {
    val condition = (x*7+y*8+z*3 === a && x*2 >= y && y*2 >= z && z*2 >= x)
    val solution = APASynthesis.solve("extract7and8", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def extractRatio() {
    val condition = (y*b === c || y*c === b)
    val solution = APASynthesis.solve("extractRatio", condition)
    println(solution._1)
    println(solution._2)
  }
  def APAExample() {
    val condition = (x*(-2)+y*a+1 <= 0 && x*b+y*3 + (-1) >= 0)
    val solution = APASynthesis.solve("APAExample", condition)
    println(solution._1)
    println(solution._2)
  }
  
  def multiArray() {
    val x = I("x")
    val y = I("y")
    val c = O("c")
    val i = O("i")
    val j = O("j")
    val condition = ((c + (i + j*640)*3 === x + y*1024) && c >= 0 && c < 3 && i >= 0 && i < 640 && j >= 0 && j < 480 && x >= 0 && x < 1024) 
    val solution = APASynthesis.solve("multiArray", condition)
    println(solution._1)
    println(solution._2)
  }

  def paboucle() {
    val a = I("a")
    val condition = c - y <= a - x*6 && a - x*6 <= b + x + y*7  &&  x > y + z && z*9 <= x+y && z*5 > b + x + 8
    val solution = APASynthesis.solve("paboucle", condition)
    println(solution._1)
    println(solution._2)
  }
}
