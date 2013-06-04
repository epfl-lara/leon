/* Copyright 2009-2013 EPFL, Lausanne */

package leon.testgen

import leon.purescala.Definitions._
import leon.purescala.Trees._
import leon.xlang.Trees._
import leon.purescala.TreeOps._
import leon.purescala.Extractors._
import leon.purescala.TypeTrees._
import leon.purescala.Common._
import leon.solvers.z3.FairZ3Solver

class CallGraph(val program: Program) {

  sealed abstract class ProgramPoint
  case class FunctionStart(fd: FunDef) extends ProgramPoint
  case class ExpressionPoint(wp: Expr, id: Int) extends ProgramPoint
  private var epid = -1
  private def freshExpressionPoint(wp: Expr) = {epid += 1; ExpressionPoint(wp, epid)}

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
      val subgraph = collectWithPathCondition(cleanBody, FunctionStart(fd))
      callGraph ++= subgraph
    })

    callGraph = addFunctionInvocationsEdges(callGraph)

    callGraph = simplifyGraph(callGraph)

    callGraph
  }

  private def simplifyGraph(graph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]]): Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    def fix[A](f: (A) => A, a: A): A = {
      val na = f(a)
      if(a == na) a else fix(f, na)
    }
    fix(compressGraph, graph)
  }

  //does a one level compression of the graph
  private def compressGraph(graph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]]): Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    var newGraph = graph

    graph.find{
      case (point, edges) => {
        edges.exists{
          case edge@(p2@ExpressionPoint(e, _), TransitionLabel(BooleanLiteral(true), assign)) if assign.isEmpty && !e.isInstanceOf[Waypoint] => {
            val edgesOfPoint: Set[(ProgramPoint, TransitionLabel)] = graph.get(p2).getOrElse(Set()) //should be unique entry point and cannot be a FunctionStart
            newGraph += (point -> ((edges - edge) ++ edgesOfPoint))
            newGraph -= p2
            true 
          }
          case _ => false
        }
      }
    }

    newGraph
  }


  private def addFunctionInvocationsEdges(graph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]]): Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    var augmentedGraph = graph

    graph.foreach{ 
      case (point@ExpressionPoint(FunctionInvocation(fd, args), _), edges) => {
        val newPoint = FunctionStart(fd)
        val newTransition = TransitionLabel(BooleanLiteral(true), fd.args.zip(args).map{ case (VarDecl(id, _), arg) => (id.toVariable, arg) }.toMap)
        augmentedGraph += (point -> (edges + ((newPoint, newTransition))))
      }
      case _ => ;
    }

    augmentedGraph
  }

  private def collectWithPathCondition(expression: Expr, startingPoint: ProgramPoint): Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = {
    var callGraph: Map[ProgramPoint, Set[(ProgramPoint, TransitionLabel)]] = Map()

    def rec(expr: Expr, path: List[Expr], startingPoint: ProgramPoint): Unit = {
      val transitions: Set[(ProgramPoint, TransitionLabel)] = callGraph.get(startingPoint) match {
        case None => Set()
        case Some(s) => s
      }
      expr match {
        //case FunctionInvocation(fd, args) => {
        //  val newPoint = FunctionStart(fd)
        //  val newTransition = TransitionLabel(And(path.toSeq), fd.args.zip(args).map{ case (VarDecl(id, _), arg) => (id.toVariable, arg) }.toMap)
        //  callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
        //  args.foreach(arg => rec(arg, path, startingPoint))
        //}
        //this case is actually now handled in the unaryOp case
        //case way@Waypoint(i, e) => {
        //  val newPoint = ExpressionPoint(way)
        //  val newTransition = TransitionLabel(And(path.toSeq), Map())
        //  callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
        //  rec(e, List(), newPoint)
        //}
        case IfExpr(cond, thenn, elze) => {
          rec(cond, path, startingPoint)
          rec(thenn, cond :: path, startingPoint) 
          rec(elze, Not(cond) :: path, startingPoint)
        }
        case n@NAryOperator(args, _) => {
          val newPoint = freshExpressionPoint(n)
          val newTransition = TransitionLabel(And(path.toSeq), Map())
          callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
          args.foreach(rec(_, List(), newPoint))
        }
        case b@BinaryOperator(t1, t2, _) => {
          val newPoint = freshExpressionPoint(b)
          val newTransition = TransitionLabel(And(path.toSeq), Map())
          callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
          rec(t1, List(), newPoint)
          rec(t2, List(), newPoint) 
        }
        case u@UnaryOperator(t, _) => {
          val newPoint = freshExpressionPoint(u)
          val newTransition = TransitionLabel(And(path.toSeq), Map())
          callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
          rec(t, List(), newPoint)
        }
        case t : Terminal => {
          val newPoint = freshExpressionPoint(t)
          val newTransition = TransitionLabel(And(path.toSeq), Map())
          callGraph += (startingPoint -> (transitions + ((newPoint, newTransition))))
        }
        case _ => scala.sys.error("Unhandled tree in collectWithPathCondition : " + expr)
      }
    }

    rec(expression, List(), startingPoint)
    callGraph
  }

  //given a path, follow the path to build the logical constraint that need to be satisfiable
  def pathConstraint(path: Seq[(ProgramPoint, ProgramPoint, TransitionLabel)], assigns: List[Map[Expr, Expr]] = List()): Expr = {
    if(path.isEmpty) BooleanLiteral(true) else {
      val (_, _, TransitionLabel(cond, assign)) = path.head
      val finalCond = assigns.foldRight(cond)((map, acc) => replace(map, acc))
      And(finalCond, 
          pathConstraint(
            path.tail, 
            if(assign.isEmpty) assigns else assign.asInstanceOf[Map[Expr, Expr]] :: assigns
          )
         )
    }
  }

  private def isMain(fd: FunDef): Boolean = {
    fd.annotations.exists(_ == "main")
  }

  def findAllPaths(z3Solver: FairZ3Solver): Set[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = {
    val waypoints: Set[ProgramPoint] = programPoints.filter{ case ExpressionPoint(Waypoint(_, _), _) => true case _ => false }
    val sortedWaypoints: Seq[ProgramPoint] = waypoints.toSeq.sortWith((p1, p2) => {
      val (ExpressionPoint(Waypoint(i1, _), _), ExpressionPoint(Waypoint(i2, _), _)) = (p1, p2)
      i1 <= i2
    })

    val functionPoints: Set[ProgramPoint] = programPoints.flatMap{ case f@FunctionStart(fd) => Set[ProgramPoint](f) case _ => Set[ProgramPoint]() }
    val mainPoint: Option[ProgramPoint] = functionPoints.find{ case FunctionStart(fd) => isMain(fd) case p => sys.error("unexpected: " + p) }

    assert(mainPoint != None)

    if(sortedWaypoints.size == 0) {
      findSimplePaths(mainPoint.get)
    } else {
      visitAllWaypoints(mainPoint.get :: sortedWaypoints.toList, z3Solver) match {
        case None => Set()
        case Some(p) => Set(p)
      }
      //Set(
      //  sortedWaypoints.zip(sortedWaypoints.tail).foldLeft(Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]())((path, waypoint) =>
      //    path ++ findPath(waypoint._1, waypoint._2))
      //)
    }
  }

  def visitAllWaypoints(waypoints: List[ProgramPoint], z3Solver: FairZ3Solver): Option[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = {
    def rec(head: ProgramPoint, tail: List[ProgramPoint], path: Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]): 
      Option[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = {
        tail match {
          case Nil => Some(path)
          case x::xs => {
            val allPaths = findSimplePaths(head, Some(x))
            var completePath: Option[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = None
            allPaths.find(intermediatePath => {
              val pc = pathConstraint(path ++ intermediatePath)
              z3Solver.init()
              z3Solver.restartZ3

              var testcase: Option[Map[Identifier, Expr]] = None
                
              val (solverResult, model) = z3Solver.solveSAT(pc)
              solverResult match {
                case None => {
                  false
                }
                case Some(false) => {
                  false
                }
                case Some(true) => {
                  val recPath = rec(x, xs, path ++ intermediatePath)
                  recPath match {
                    case None => false
                    case Some(path) => {
                      completePath = Some(path)
                      true
                    }
                  }
                }
              }
            })
            completePath
          }
        }
    }
    rec(waypoints.head, waypoints.tail, Seq())
  }

  def findSimplePaths(from: ProgramPoint, to: Option[ProgramPoint] = None): Set[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = {
    def dfs(point: ProgramPoint, path: List[(ProgramPoint, ProgramPoint, TransitionLabel)], visitedPoints: Set[ProgramPoint]): 
      Set[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]] = graph.get(point) match {
        case None => Set(path.reverse)
        case Some(edges) => {
          if(to != None && to.get == point)
            Set(path.reverse)
          else if(to == None && edges.forall((edge: (ProgramPoint, TransitionLabel)) => visitedPoints.contains(edge._1) || point == edge._1))
            Set(path.reverse)
          else {
            edges.flatMap((edge: (ProgramPoint, TransitionLabel)) => {
              val (neighbour, transition) = edge
              if(visitedPoints.contains(neighbour) || point == neighbour) 
                Set[Seq[(ProgramPoint, ProgramPoint, TransitionLabel)]]()
              else
                dfs(neighbour, (point, neighbour, transition) :: path, visitedPoints + point)
            })
          }
        }
      }

    dfs(from, List(), Set())
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
      case ExpressionPoint(Waypoint(i, e), _) => "WayPoint " + i
      case ExpressionPoint(e, _) => e.toString
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

