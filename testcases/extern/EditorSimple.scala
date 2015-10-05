import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._
import scala.reflect.runtime.universe._
import scala.reflect.api.{TypeCreator, Universe, Mirror}


import scala.collection.immutable.{List => ScalaList, Nil => ScalaNil}

object Editor {
  abstract class Mode
  case object Edit extends Mode
  case object Quitted extends Mode

  case class State(line: List[Int], cursor: Int, buffer: List[Int], actions: List[Action], mode: Mode) {
    def setLine(l: List[Int]) = State(l, cursor, buffer, actions, mode)
    def setCursor(c: Int) = State(line, c, buffer, actions, mode)
    def setBuffer(b: List[Int]) = State(line, cursor, b, actions, mode)
    def addAction(a: Action) = State(line, cursor, buffer, Cons(a, actions), mode)
    def setMode(m: Mode) = State(line, cursor, buffer, actions, m)
  }

  sealed abstract class Action
  case object Unknown extends Action
  case object Write extends Action
  case object Quit extends Action
  case class MoveCursor(to: Int) extends Action
  case object Replace extends Action
  case object Erase extends Action
  case class Content(l: List[Int]) extends Action

  //@extern
  //def getCommand(): List[Int] = {
  //  print("> ")
  //  readLine().toList.map(_.toInt)
  //}

  def getCommand()(implicit o: Oracle[List[Int]]): List[Int] = {
    ???
  }

  @extern
  def unknown() = {
    println("?")
  }

  @extern
  def displayState(s: State) = {
    println("  | Line   : "+listToString(s.line))
    println("  | Cursor : "+(" "*s.cursor)+"^")
    println("  | Buffer : "+listToString(s.buffer))
    println("  | A*     : "+s.actions.collect {
        case Content(l) => "Content("+listToString(l)+")"
        case a => a.toString
      }.mkString(", "))
  }

  @extern
  def display(input: List[Int], a: Action, s: State) = {
    println("  | Input  : "+listToString(input))
    println("  | Action : "+a)
    println("  ~~~~~~~~~~~~~~~~~~~")
    displayState(s)
  }

  def replStep(state: State)(implicit o: Oracle[List[Int]]): State = {
    if (state.mode == Quitted) {
      state
    } else {
      val i = getCommand()
      val a = getAction(i, state)

      doAction(state, a)
    }
  }

  def getAction(input: List[Int], state: State): Action = {
    if (input == Cons(113, Nil())) {
      Quit
    } else if (input == Cons(100, Nil())) {
      Erase
    } else if (input == Cons(94, Nil())) {
      MoveCursor(0)
    } else if (input == Cons(36, Nil())) {
      MoveCursor(-1)
    } else if (input == Cons(114, Nil())) {
      Replace
    } else if (input == Cons(119, Nil())) {
      Write
    } else if (input.size > 1) {
      Content(input)
    } else {
      Unknown
    }
  }

  def doAction(state: State, action: Action): State = {
    val c = state.cursor
    val l = state.line


    val ns = (action, state.actions) match {
      case (Content(cnt), Cons(Write, _)) =>
        val nl = l.take(c) ++ cnt ++ l.drop(c)
        state.setLine(nl).setCursor(c + cnt.size)
      case (Content(cnt), Cons(Replace, _)) =>
        val nl = l.take(c) ++ cnt ++ l.drop(c+cnt.size)
        state.setLine(nl).setCursor(c + cnt.size)
      case (MoveCursor(i), _) =>
        if (i < 0) {
          state.setCursor(state.line.size+1+i)
        } else {
          state.setCursor(i)
        }
      case (Erase, _) =>
        state.setLine(Nil()).setCursor(0)
      case (Quit, _) =>
        state.setMode(Quitted)
      case (Unknown, _) =>
        //unknown()
        state
      case _ =>
        state
    }

    ns.addAction(action)
  }

  def repl() = {
    val finalState = {
      withOracle { implicit o: Oracle[List[Int]] =>
        {
          val state = State(Nil(), 0, Nil(), Nil(), Edit)
          val res = replStep(replStep(replStep(state)(o.left))(o.right.left))(o.right.right.left)
          val tmp = displayState(res)
          res
        } ensuring {
          s => s.line == Cons(97, Cons(97, Cons(97, Nil()))) && s.mode == Quitted
        }
      }
    }
    finalState
  }

  @ignore
  @extern
  implicit def scalaToList[T](l: ScalaList[T]): List[T] = {
    l.foldRight[List[T]](Nil())( (e, l) => Cons(e, l) )
  }

  @ignore
  @extern
  implicit def listToScala[T](l: List[T]): ScalaList[T] = l match {
    case Nil() => ScalaNil
    case Cons(h, t) => h :: listToScala(t)
  }

  @ignore
  @extern
  implicit def listToString(l: List[Int]): String = {
    l.map(_.toChar).mkString("")
  }

  @ignore
  @extern
  def asList(l: String): List[Int] = {
    l.toList.map(_.toInt)
  }
}
