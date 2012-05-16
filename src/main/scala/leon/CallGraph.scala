package leon

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.purescala.TypeTrees._
import leon.purescala.Common._

class CallGraph(val program: Program) {

  sealed abstract class ProgramPoint
  case class FunctionStart(fd: FunDef) extends ProgramPoint
  case class ExpressionPoint(wp: Expr) extends ProgramPoint

  //sealed abstract class EdgeLabel
  //case class ConditionLabel(expr: Expr) extends EdgeLabel {
  //  require(expr.getType == BooleanType)
  //}
  //case class FunctionInvocLabel(fd: FunDef, args: List[Expr]) extends EdgeLabel {
  //  require(args.zip(fd.args).forall(p => p._1.getType == p._2.getType))
  //}
  case class TransitionLabel(cond: Expr, assignment: Map[Variable, Expr])

  private lazy val graph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = buildGraph
  private lazy val programPoints: Set[ProgramPoint] = {
    graph.flatMap(pair => pair._2.map(edge => edge._1).toSet + pair._1).toSet
  }

  private def buildGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    var callGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = Map()

    program.definedFunctions.foreach(fd => {
      val body = fd.body.get 
      //val cleanBody = hoistIte(expandLets(matchToIfThenElse(body)))
      val cleanBody = expandLets(matchToIfThenElse(body))
      //println(cleanBody)
      val subgraph = collectWithPathCondition(cleanBody, FunctionStart(fd))
      //println(subgraph)
      callGraph ++= subgraph
    })

    //println(callGraph)

    callGraph
  }

  private def collectWithPathCondition(expression: Expr, startingPoint: ProgramPoint): Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    var callGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = Map()

    def rec(expr: Expr, path: List[Expr], startingPoint: ProgramPoint): Unit = expr match {
      case FunctionInvocation(fd, args) => {
        val transitions: Set[(ProgramPoint, TransitionLabel)] = callGraph.get(startingPoint) match {
          case None => Set()
          case Some(s) => s
        }
        val newPoint = FunctionStart(fd)
        val newTransition = TransitionLabel(And(path.toSeq), fd.args.zip(args).map{ case (VarDecl(id, _), arg) => (id.toVariable, arg) }.toMap)
        callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
        args.foreach(arg => rec(arg, path, startingPoint))
      }
      case way@Waypoint(i, e) => {
        val transitions: Set[(ProgramPoint, TransitionLabel)] = callGraph.get(startingPoint) match {
          case None => Set()
          case Some(s) => s
        }
        val newPoint = ExpressionPoint(way)
        val newTransition = TransitionLabel(And(path.toSeq), Map())
        callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
        rec(e, List(), newPoint)
      }
      case IfExpr(cond, then, elze) => {
        rec(cond, path, startingPoint)
        rec(then, cond :: path, startingPoint) 
        rec(elze, Not(cond) :: path, startingPoint)
      }
      case NAryOperator(args, _) => args.foreach(rec(_, path, startingPoint))
      case BinaryOperator(t1, t2, _) => rec(t1, path, startingPoint); rec(t2, path, startingPoint)
      case UnaryOperator(t, _) => rec(t, path, startingPoint)
      case t : Terminal => ;
      case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
    }

    rec(expression, List(), startingPoint)

    callGraph
  }

  //given a path, follow the path to build the logical constraint that need to be satisfiable
  def pathConstraint(path: Seq[(ProgramPoint, ProgramPoint, TransitionLabel)], assigns: List[Map[Expr, Expr]] = List()): Expr = {
    if(path.isEmpty) BooleanLiteral(true) else {
      val (_, _, TransitionLabel(cond, assign)) = path.head
      val finalCond = assigns.foldRight(cond)((map, acc) => replace(map, acc))
      And(finalCond, pathConstraint(path.tail, assign.asInstanceOf[Map[Expr, Expr]] :: assigns))
    }
  }

  def findAllPathes: Set[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = {
    val waypoints: Set[ProgramPoint] = programPoints.filter{ case ExpressionPoint(_) => true case _ => false }
    val sortedWaypoints: Seq[ProgramPoint] = waypoints.toSeq.sortWith((p1, p2) => {
      val (ExpressionPoint(Waypoint(i1, _)), ExpressionPoint(Waypoint(i2, _))) = (p1, p2)
      i1 <= i2
    })
    Set(
      sortedWaypoints.zip(sortedWaypoints.tail).foldLeft(Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]())((path, waypoint) =>
        path ++ findPath(waypoint._1, waypoint._2))
    )
  }

  //find a path that goes through all waypoint in order
  def findPath(from: ProgramPoint, to: ProgramPoint): Seq[(ProgramPoint, ProgramPoint, TransitionLabel)] = {
    var visitedPoints: Set[ProgramPoint] = Set()
    var history: Map[ProgramPoint, (ProgramPoint, TransitionLabel)] = Map()
    var toVisit: List[ProgramPoint] = List(from)

    var currentPoint: ProgramPoint = null
    while(!toVisit.isEmpty && currentPoint != to) {
      currentPoint = toVisit.head
      if(currentPoint != to) {
        visitedPoints += currentPoint
        toVisit = toVisit.tail
        graph.get(currentPoint).foreach(edges => edges.foreach{
          case (neighbour, transition) =>
            if(!visitedPoints.contains(neighbour) && !toVisit.contains(neighbour)) {
              toVisit ::= neighbour
              history += (neighbour -> ((currentPoint, transition)))
            }
        })
      }
    }

    def rebuildPath(point: ProgramPoint, path: List[(ProgramPoint, ProgramPoint, TransitionLabel)]): Seq[(ProgramPoint, ProgramPoint, TransitionLabel)] = {
      if(point == from) path else {
        val (previousPoint, transition) = history(point)
        val newPath = (previousPoint, point, transition) :: path
        rebuildPath(previousPoint, newPath)
      }
    }

    //TODO: handle case where the target node is not found
    rebuildPath(to, List())
  }

  //guarentee that all IfExpr will be at the top level and as soon as you encounter a non-IfExpr, then no more IfExpr can be find in the sub-expressions
  def hoistIte(expr: Expr): Expr = {
    def transform(expr: Expr): Option[Expr] = expr match {
      case uop@UnaryOperator(IfExpr(c, t, e), op) => Some(IfExpr(c, op(t).setType(uop.getType), op(e).setType(uop.getType)).setType(uop.getType))
      case bop@BinaryOperator(IfExpr(c, t, e), t2, op) => Some(IfExpr(c, op(t, t2).setType(bop.getType), op(e, t2).setType(bop.getType)).setType(bop.getType))
      case bop@BinaryOperator(t1, IfExpr(c, t, e), op) => Some(IfExpr(c, op(t1, t).setType(bop.getType), op(t1, e).setType(bop.getType)).setType(bop.getType))
      case nop@NAryOperator(ts, op) => {
        val iteIndex = ts.indexWhere{ case IfExpr(_, _, _) => true case _ => false }
        if(iteIndex == -1) None else {
          val (beforeIte, startIte) = ts.splitAt(iteIndex)
          val afterIte = startIte.tail
          val IfExpr(c, t, e) = startIte.head
          Some(IfExpr(c,
            op(beforeIte ++ Seq(t) ++ afterIte).setType(nop.getType),
            op(beforeIte ++ Seq(e) ++ afterIte).setType(nop.getType)
          ).setType(nop.getType))
        }
      }
      case _ => None
    }

    def fix[A](f: (A) => A, a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f, na)
    }
    fix(searchAndReplaceDFS(transform), expr)
  }


  lazy val toDotString: String = {
    var vertexLabels: Set[(String, String)] = Set()
    var vertexId = -1
    var point2vertex: Map[ProgramPoint, Int] = Map()
    //return id and label
    def getVertex(p: ProgramPoint): (String, String) = point2vertex.get(p) match {
      case Some(id) => ("v_" + id, ppPoint(p))
      case None => {
        vertexId += 1
        point2vertex += (p -> vertexId)
        val pair = ("v_" + vertexId, ppPoint(p))
        vertexLabels += pair
        pair
      }
    }

    def ppPoint(p: ProgramPoint): String = p match {
      case FunctionStart(fd) => fd.id.name
      case ExpressionPoint(Waypoint(i, e)) => "WayPoint " + i
      case _ => sys.error("Unexpected programPoint: " + p)
    }
    def ppLabel(l: TransitionLabel): String = {
      val TransitionLabel(cond, assignments) = l
      cond.toString + ", " + assignments.map(p => p._1 + " -> " + p._2).mkString("\n")
    }

    val edges: List[(String, String, String)] = graph.flatMap(pair => {
      val (startPoint, edges) = pair
      val (startId, _) = getVertex(startPoint)
      edges.map(pair => {
        val (endPoint, label) = pair
        val (endId, _) = getVertex(endPoint)
        (startId, endId, ppLabel(label))
      }).toList
    }).toList

    val res = (
      "digraph " + program.id.name + " {\n" +
      vertexLabels.map(p => p._1 + " [label=\"" + p._2 + "\"];").mkString("\n") + "\n" +
      edges.map(p => p._1 + " -> " + p._2 + " [label=\"" + p._3 + "\"];").mkString("\n") + "\n" +
      "}")

    res
  }

  def writeDotFile(filename: String) {
    import java.io.FileWriter
    import java.io.BufferedWriter
    val fstream = new FileWriter(filename)
    val out = new BufferedWriter(fstream)
    out.write(toDotString)
    out.close
  }

}

  //def hoistIte(expr: Expr): (Seq[Expr] => Expr, Seq[Expr]) = expr match { 
  //  case ite@IfExpr(c, t, e) => {
  //    val (iteThen, valsThen) = hoistIte(t)
  //    val nbValsThen = valsThen.size
  //    val (iteElse, valsElse) = hoistIte(e)
  //    val nbValsElse = valsElse.size
  //    def ite(es: Seq[Expr]): Expr = {
  //      val argsThen = es.take(nbValsThen)
  //      val argsElse = es.drop(nbValsThen)
  //      IfExpr(c, iteThen(argsThen), iteElse(argsElse), e2)
  //    }
  //    (ite, valsThen ++ valsElse)
  //  }
  //  case BinaryOperator(t1, t2, op) => {
  //    val (iteLeft, valsLeft) = hoistIte(t1)
  //    val (iteRight, valsRight) = hoistIte(t2)
  //    def ite(e1: Expr, e2: Expr): Expr = {

  //    }
  //    iteLeft(
  //      iteRight(
  //        op(thenValRight, thenValLeft),
  //        op(thenValRight, elseValLeft)
  //      ), iteRight(
  //        op(elseValRight, thenValLeft),
  //        op(elseValRight, elseValLeft)
  //      )
  //    )
  //  }
  //  case NAryOperator(args, op) => {

  //  }
  //  case (t: Terminal) => {
  //    def ite(es: Seq[Expr]): Expr = {
  //      require(es.size == 1)
  //      es.head
  //    }
  //    (ite, Seq(t))
  //  }
  //  case _ => scala.sys.error("Unhandled tree in hoistIte : " + expr)
  //}

