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

    // Simple over aproximation of the distance
    def distance(o: Pos) = {
      val dx = o.x-x
      val dy = o.y-y

      (dx*dx + dy*dy)
    }

    def update(a: Action) = a match {
      case MoveUp =>
        up
      case MoveDown =>
        down
      case MoveLeft =>
        left
      case MoveRight =>
        right
      case Noop =>
        this
    }
  }

  case class Map(walls: Set[Pos], size: Pos) {
    // Returns whether a certain position is a valid position to be in given
    // the map
    def isValidPos(p: Pos): Boolean = {
      p.x >= 0 && p.y >= 0 &&
      p.x < size.x && p.y < size.y &&
      !(walls contains p)
    }

    def allValidPos(lp: List[Pos]): Boolean = lp match {
      case Cons(h, t) => isValidPos(h) && allValidPos(t)
      case Nil() => true
    }
  }

  abstract class Action;
  case object MoveUp extends Action
  case object MoveDown extends Action
  case object MoveLeft extends Action
  case object MoveRight extends Action
  case object Noop extends Action

  case class Game(player: Pos,
                  monsters: List[Pos],
                  map: Map) {

    def isValidAction(pos: Pos, action: Action) = {
      val np = pos.update(action)
      map.isValidPos(np)
    }

    def isDead = {
      isAtPositions(player, monsters)
    }

    def isAtPositions(p: Pos, lp: List[Pos]): Boolean = lp match {
      case Cons(h,t) => (h == p) || isAtPositions(p, t)
      case _ => false
    }

    def isValid = {
      map.isValidPos(player) &&
      map.allValidPos(monsters)
    }

    def isRunning = !isDead
  }

  def step(g: Game)(implicit o: Oracle[Action]): Game = {
    if (g.isDead) {
      g
    } else {
      val g1 = stepPlayer(g)
      Game(g1.player, stepMonsters(g1, g1.monsters), g1.map)
    }
  }

  def gameStep(g: Game)(implicit o: Oracle[Action]): Game = {
    val u = display(g)
    //withOracle { implicit o: Oracle[Action] => {
      step(g)
    //} ensuring { g => !g.isDead }}
  }

  def play(g: Game)(implicit o: Oracle[Action]): Game = {
    val r = gameStep(g)(o.left)
    if (r.isDead) {
      r
    } else {
      play(r)(o.left)
    }
  }


  def stepMonster(g: Game, oldPos: Pos): Pos = {
    val a = choose { a: Action =>
      bestTowards(g, oldPos, a, g.player)
    }

    oldPos.update(a)
  }

  def stepPlayer(g: Game)(implicit o: Oracle[Action]) = {
    //withOracle { implicit o: Oracle[Action] => {
      val action: Action = ???

      val np = g.player.update(action)

      Game(if (g.map.isValidPos(np)) np else g.player, g.monsters, g.map)
    //} ensuring { g => !g.isDead }}
  }

  def bestTowards(g: Game, old: Pos, action: Action, target: Pos): Boolean = {
    def metric(a: Action): Int = {
      old.update(a).distance(target)
    }

    def betterThan(a: Action, other: Action): Boolean = {
      !g.isValidAction(old, other) || (metric(a) <= metric(other))
    }

    g.isValidAction(old, action) &&
    betterThan(action, MoveUp) &&
    betterThan(action, MoveDown) &&
    betterThan(action, MoveLeft) &&
    betterThan(action, MoveRight) &&
    betterThan(action, Noop)
  }

  def stepMonsters(g: Game, lp: List[Pos]): List[Pos] = lp match {
    case Cons(h,t) => Cons(stepMonster(g, h), stepMonsters(g, t))
    case Nil() => Nil()
  }

  @extern
  def display(g: Game): Int = {
    print("\033[2J\033[1;1H")
    print("   ")
    for (x <- 0 until g.map.size.x) {
      print(x)
    }
    println
    print("  ╔")
    for (x <- 0 until g.map.size.x) {
      print('═')
    }
    println('╗')
    for (y <- 0 until g.map.size.y) {
      print(y+" ║")
      for (x <- 0 until g.map.size.x) {
        val c = Pos(x,y)
        if (g.map.walls contains c) {
          print('▒')
        } else if (g.player == c) {
          if (g.isDead) {
            print(Console.RED+Console.BOLD+"☠"+Console.RESET)
          } else {
            print(Console.GREEN+"☺"+Console.RESET)
          }
        } else if (g.isAtPositions(c, g.monsters)) {
          print(Console.RED+"X"+Console.RESET)
        } else {
          print(" ")
        }
      }
      println('║')
    }
    print("  ╚")
    for (x <- 0 until g.map.size.x) {
      print('═')
    }
    println('╝')

    42
  }

  @ignore
  def foreach[A](l: List[A], f: A => Unit): Unit = l match {
    case Cons(h, t) => f(h); foreach(t, f)
    case Nil() =>
  }

  @extern
  abstract class OracleSource[T] extends Oracle[T] {
    def branch: OracleSource[T]
    def value: T

    lazy val v: T = value
    lazy val l: OracleSource[T] = branch
    lazy val r: OracleSource[T] = branch

    override def head: T = v
    override def left: Oracle[T] = l
    override def right: Oracle[T] = r
  }

  @extern
  class Keyboard extends OracleSource[Action] {
    def branch = new Keyboard
    def value = {
      import scala.tools.jline._

      var askAgain = false
      var action: Action = Noop

      val t = new UnixTerminal()

      try {
        t.init()

        do {
          if (askAgain) println("?")
          askAgain = false

          t.readVirtualKey(System.in) match {
            case 16 =>
              action = MoveUp
            case 14 =>
              action = MoveDown
            case 6 =>
              action = MoveRight
            case 2 =>
              action = MoveLeft
            case a =>
              println("Got "+a)
              askAgain = true
          }

        } while(askAgain)

      } finally {
        t.restore()
      }

      action
    }
  }

  @extern
  class Random extends OracleSource[Action] {
    def value = {
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

  @extern
  def getOracle(): Oracle[Action] = {
    new Keyboard
  }

  @extern
  def pause(): Unit = {
    readLine
  }

  def start() = {
    val map  = Map(Set(Pos(2,2), Pos(2,3), Pos(4,4), Pos(5,5)), Pos(10,10))
    val monsters = Cons(Pos(8,5), Cons(Pos(6,2), Nil()))
    val init = Game(Pos(0,0), monsters, map)

    val res = play(init)(getOracle())

    val tmp = display(res)

    res
  }
}
