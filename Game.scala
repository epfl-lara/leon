import leon.lang._
import leon.annotation._
import leon.lang.synthesis._
import leon.collection._

object Test {
  case class Pos(x: Int, y: Int) {
    def up      = Pos(x, y-1)
    def down    = Pos(x, y+1)
    def left    = Pos(x-1, y)
    def right   = Pos(x+1, y)

    def isValid(s: State) = {
      x >= 0 && y >= 0 &&
      x < s.map.size.x && y < s.map.size.y &&
      !(s.map.walls contains this)
    }

    def distance(o: Pos) = {
      (if (o.x < x) (x-o.x) else (o.x-x)) +
      (if (o.y < y) (y-o.y) else (o.y-y))
    }
  }

  case class Map(walls: Set[Pos], size: Pos)

  abstract class Action;
  case object MoveUp extends Action
  case object MoveDown extends Action
  case object MoveLeft extends Action
  case object MoveRight extends Action
  case object Quit extends Action

  case class State(pos: Pos,
                   monster: Pos,
                   stop: Boolean,
                   map: Map) {

    def isValid = {
      pos.isValid(this) && monster.isValid(this)
    }

   }

  def step(s: State)(implicit o: Oracle[Action]): State = {
    require(s.isValid)

    val u = display(s)

    stepMonster(stepPlayer(s)(o.left))
  }

  def stepMonster(s: State) = {
    require(s.isValid)
    if (s.pos == s.monster) {
      State(s.pos, s.monster, true, s.map)
    } else {
      val mp = choose {
        (res: Pos) =>
          res.distance(s.monster) <= 1 &&
          res.distance(s.pos) <= s.monster.distance(s.pos) &&
          res.isValid(s)
      }
      State(s.pos, mp, mp != s.pos, s.map)
    }
  } ensuring { _.isValid }

  def stepPlayer(s: State)(implicit o: Oracle[Action]) = {
    val action: Action = ???

    val ns = action match {
      case Quit =>
        State(s.pos, s.monster, true, s.map)
      case _ if s.stop =>
        s
      case MoveUp if s.pos.y > 0 =>
        State(s.pos.up, s.monster, s.stop, s.map)
      case MoveDown =>
        State(s.pos.down, s.monster, s.stop, s.map)
      case MoveLeft if s.pos.x > 0 =>
        State(s.pos.left, s.monster, s.stop, s.map)
      case MoveRight =>
        State(s.pos.right, s.monster, s.stop, s.map)
      case _ =>
        s
    }

    if (ns.isValid) ns else s
  }

  def steps(s: State, b: Int)(implicit o: Oracle[Action]): State = {
    if (b == 0 || s.stop) {
      s
    } else {
      steps(step(s)(o), b-1)(o.right)
    }
  }

  def play(s: State)(implicit o: Oracle[Action]): State = {
    steps(s, -1)
  }

  @extern
  def display(s: State): Int = {
    print('╔')
    for (x <- 0 until s.map.size.x) {
      print('═')
    }
    println('╗')
    for (y <- 0 until s.map.size.y) {
      print('║')
      for (x <- 0 until s.map.size.x) {
        val c = Pos(x,y)
        if (s.map.walls contains c) {
          print('X')
        } else if (s.pos == c) {
          print('o')
        } else if (s.monster == c) {
          print('m')
        } else {
          print(" ")
        }
      }
      println('║')
    }
    print('╚')
    for (x <- 0 until s.map.size.x) {
      print('═')
    }
    println('╝')

    42
  }

  @extern
  def main(args: Array[String]) {

    abstract class OracleSource[T] extends Oracle[T] {
      def branch: OracleSource[T]
      def value: T

      lazy val v: T = value
      lazy val l: OracleSource[T] = branch
      lazy val r: OracleSource[T] = branch

      override def head = v
      override def left = l
      override def right = r
    }

    class Keyboard extends OracleSource[Action] {
      def branch = new Keyboard
      def value = {
        var askAgain = false
        var action: Action = Quit
        do {
          if (askAgain) println("?")
          askAgain = false
          print("> ")
          readLine().trim match {
            case "up" =>
              action = MoveUp
            case "down" =>
              action = MoveDown
            case "left" =>
              action = MoveLeft
            case "right" =>
              action = MoveRight
            case "quit" =>
              action = Quit
            case _ =>
              askAgain = true
          }
        } while(askAgain)

        action
      }
    }

    class Random extends OracleSource[Action] {
      def value = {
        readLine()
        scala.util.Random.nextInt(4) match {
          case 0 =>
            MoveUp
          case 1 =>
            MoveDown
          case 2 =>
            MoveLeft
          case 3 =>
            MoveRight
          case _ =>
            MoveUp
        }
      }

      def branch = new Random
    }

    val map  = Map(Set(Pos(2,2), Pos(2,3), Pos(4,4), Pos(5,5)), Pos(10,10))
    val init = State(Pos(0,0), Pos(4,5), false, map)

    play(init)(new Random)
  }

  def test1() = {
    withOracle{ o: Oracle[Action] =>
      {
        val map  = Map(Set(Pos(2,2), Pos(2,3), Pos(4,4), Pos(5,5)), Pos(10,10))
        val init = State(Pos(0,0), Pos(4,4), false, map)

        steps(init, 5)(o)
      } ensuring {
        _.pos == Pos(0,3)
      }
    }
  }

  def validStep(s: State) = {
    require(s.map.size.x > 3 &&  s.map.size.y > 3 && s.pos != s.monster && s.isValid && !s.stop)

    val ns = withOracle { o: Oracle[Action] =>
      {
        stepPlayer(s)(o)
      } ensuring {
        res => res.isValid && !res.stop
      }
    }
    stepMonster(ns)
  } ensuring {
    res => res.isValid && !res.stop
  }
}
