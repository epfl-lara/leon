// Developed by Etienne Kneuss, 2015
import leon.lang._
import leon.collection._
import leon.annotation._

object Robot {

  // From top left
  case class Position(x: BigInt, y: BigInt) {
    def +(o: Orientation) = o match {
      case North => Position(x, y-1)
      case East  => Position(x+1, y)
      case South => Position(x, y+1)
      case West  => Position(x-1, y)
    }

    def neighbors: List[Position] = {
      List(this + North, this + East, this + South, this + West)
    }
  }

  abstract class Orientation {
    def left = this match {
      case North => West
      case East  => North
      case South => East
      case West  => South
    }

    def right = this match {
      case North => East
      case East  => South
      case South => West
      case West  => North
    }
  }

  case object North extends Orientation
  case object East  extends Orientation
  case object South extends Orientation
  case object West  extends Orientation

  abstract class FireLevel {
    def level: BigInt = this match {
      case NoFire => 0
      case Fire1 => 1
      case Fire2 => 2
      case Fire3 => 3
      case Fire4 => 4
      case Fire5 => 5
    }

    def increase = this match {
      case NoFire => NoFire
      case Fire1 => Fire2
      case Fire2 => Fire3
      case Fire3 => Fire4
      case Fire4 => Fire5
      case Fire5 => Fire5
    }

    def temp:BigInt = level*100
  }

  case object NoFire extends FireLevel
  case object Fire1 extends FireLevel
  case object Fire2 extends FireLevel
  case object Fire3 extends FireLevel
  case object Fire4 extends FireLevel
  case object Fire5 extends FireLevel

  case class World(
    clock: BigInt,
    dimentions: Position,
    walls: Set[Position],
    persons: Set[Position],
    initFires: Set[Position],
    rs: RobotState) {

    def personAt(pos: Position): Boolean = persons contains pos

    def wallAt(pos: Position): Boolean = walls contains pos

    def fireAt(pos: Position): FireLevel = {
      val step = clock/50

      if (wallAt(pos)) {
        NoFire
      } else if (initFires contains pos) {
        fireLevel(clock/10+1)
      } else if (step >= 1 && (pos.neighbors.exists { p => initFires contains p })) {
        fireLevel((clock-50)/10+1)
      } else {
        NoFire
      }
    }

    def fireLevel(l: BigInt) = {
      if (l <= 1) Fire1
      else if (l <= 2) Fire2
      else if (l <= 3) Fire3
      else if (l <= 4) Fire4
      else Fire5
    }

    def isWithinMap(p: Position): Boolean = {
      p.x >= 0 && p.x < dimentions.x &&
      p.y >= 0 && p.y < dimentions.y
    }
  }


  /*******************************************************************
   * Engine Component
   *******************************************************************/

  case class EngineState(pos: Position, dim: Position, orient: Orientation)

  abstract class EngineTransition
  case object EForward extends EngineTransition
  case object ERotateLeft extends EngineTransition
  case object ERotateRight extends EngineTransition
  case object EIdle        extends EngineTransition

  def engineStep(es: EngineState, t: EngineTransition) = t match {
    case EForward     => EngineState(es.pos + es.orient, es.dim, es.orient)
    case ERotateRight => EngineState(es.pos, es.dim, es.orient.right)
    case ERotateLeft  => EngineState(es.pos, es.dim, es.orient.left)
    case EIdle        => es
  }

  def engineSucc(es: EngineState): List[EngineTransition] = {
    if ((es.pos.x <= 0 && es.orient == West) ||
        (es.pos.y <= 0 && es.orient == North) ||
        (es.pos.x >= es.dim.x && es.orient == East) ||
        (es.pos.y >= es.dim.y && es.orient == South)) {
      List(ERotateLeft, ERotateRight, EIdle)
    } else {
      List(EForward, ERotateLeft, ERotateRight, EIdle)
    }
  }

  /*******************************************************************
   * Navigation Sensor Component
   *******************************************************************/

  case class NavSensorState(wall: Option[Boolean], person: Option[Boolean]) {
    def hasData = wall.isDefined && person.isDefined

    def validData(implicit w: World) = {
      val posFront = w.rs.es.pos + w.rs.es.orient

      val wallOk = wall match {
        case Some(wal) => wal == w.wallAt(posFront)
        case None() => true
      }

      val personOk = person match {
        case Some(per) => per == w.personAt(posFront)
        case None() => true
      }

      wallOk && personOk
    }
  }

  abstract class NavSensorTransition
  case object NSense   extends NavSensorTransition
  case object NForget  extends NavSensorTransition
  case object NIdle    extends NavSensorTransition


  def navSensorStep(ns: NavSensorState, t: NavSensorTransition)(implicit w: World) = t match {
    case NSense  =>
      // Driver call
      val p = w.rs.es.pos + w.rs.es.orient
      NavSensorState(Some(w.wallAt(p)), Some(w.personAt(p)))

    case NForget =>
      NavSensorState(None(), None())

    case NIdle   =>
      ns
  }

  def navSensorSucc(ns: NavSensorState): List[NavSensorTransition] = {
    if (ns.hasData) {
      List(NForget, NIdle)
    } else {
      List(NSense, NIdle)
    }
  }

  /*******************************************************************
   * Heat Sensor Component
   *******************************************************************/

  case class HeatSensorState(heat: Option[FireLevel]) {
    def hasData = heat.isDefined

    def validData(implicit w: World) = {
      heat match {
        case Some(f) =>
          val realF = w.fireAt(w.rs.es.pos + w.rs.es.orient)
          realF == f || realF == f.increase
        case None() =>
          true
      }
    }
  }

  abstract class HeatSensorTransition
  case object HSense   extends HeatSensorTransition
  case object HForget  extends HeatSensorTransition
  case object HIdle    extends HeatSensorTransition

  def heatSensorStep(hs: HeatSensorState, t: HeatSensorTransition)(implicit w: World) = t match {
    case HSense  =>
      // Driver call
      val p = w.rs.es.pos+w.rs.es.orient
      HeatSensorState(Some(w.fireAt(p)))

    case HForget =>
      HeatSensorState(None())

    case HIdle   =>
      hs
  }

  def heatSensorSucc(hs: HeatSensorState): List[HeatSensorTransition] = {
    if (hs.hasData) {
      List(HForget, HIdle)
    } else {
      List(HSense, HIdle)
    }
  }

  /*******************************************************************
   * Transmission Component
   *******************************************************************/

  case class TransmitterState(beacon: Option[Position]) {
    def hasData = beacon.isDefined
  }

  abstract class TransmitterTransition
  case object TRepeat   extends TransmitterTransition
  case object TFound    extends TransmitterTransition
  case object TIdle     extends TransmitterTransition

  def transmitterStep(ts: TransmitterState, es: EngineState, t: TransmitterTransition)(implicit w: World) = t match {
    case TRepeat  =>
      // Driver call to transmit
      ts

    case TFound =>
      // Driver call to transmit
      TransmitterState(Some(es.pos + es.orient))

    case TIdle =>
      ts
  }

  def transmitterSucc(ts: TransmitterState): List[TransmitterTransition] = {
    if (ts.hasData) {
      List(TRepeat, TFound)
    } else {
      List(TFound, TIdle)
    }
  }


  /*******************************************************************
   * Robot Component
   *******************************************************************/

  case class RobotState(
    es: EngineState,
    ns: NavSensorState,
    hs: HeatSensorState,
    ts: TransmitterState
  )

  case class RobotTransition(
    et: EngineTransition,
    nst: NavSensorTransition,
    hst: HeatSensorTransition,
    tt: TransmitterTransition
  )

  def robotSucc(rs: RobotState): List[RobotTransition] = {
    val ess  = engineSucc(rs.es)
    val nss  = navSensorSucc(rs.ns)
    val hss  = heatSensorSucc(rs.hs)
    val ts   = transmitterSucc(rs.ts)

    filterValid(rs, ||(ess, nss, hss, ts))
  } ensuring {
    res => allValid(rs, res)
  }

  def robotStep(rs: RobotState, rt: RobotTransition)(implicit w: World): RobotState = {
    RobotState(
      engineStep(rs.es, rt.et),
      navSensorStep(rs.ns, rt.nst),
      heatSensorStep(rs.hs, rt.hst),
      transmitterStep(rs.ts, rs.es, rt.tt)
    )
  }

  // Can wistand up to 300 degrees
  def safetyTemp:BigInt = 300

  // Temperature can increase by at most 100 degree while the robot moves
  def dTempMax:BigInt = 100

  // Glue that compose sensors, transmitter and engine to perform valid actions
  def validTransition(rs: RobotState, rt: RobotTransition): Boolean = {

    // 6) Sensors must be based on recent data
    val freshSensors = if (rt.et == EForward || rt.et == ERotateRight || rt.et == ERotateLeft) {
      rt.nst == NForget && rt.hst == HForget
    } else {
      true
    }

    val freshSensors2 = if(rs.hs.hasData) {
      rt.hst == HForget
    } else {
      true
    }

    // 2/3) We can move forward only if no wall was detected
    val forwardIfNoWall = (!(rt.et == EForward) || rs.ns.wall == Some(false))

    // 3) We don't exit the world
    val forwardIfNotOutOfMap = if (rt.et == EForward) {
      (rs.es.pos.x > 0 || rs.es.orient != West) &&
      (rs.es.pos.y > 0 || rs.es.orient != North) &&
      (rs.es.pos.x < rs.es.dim.x-1 || rs.es.orient != East) &&
      (rs.es.pos.y < rs.es.dim.y-1 || rs.es.orient != South)
    } else {
      true
    }

    // 4) We can move forward only if the cell is within heat limits
    val forwardIfNotHot = (!(rt.et == EForward) || rs.hs.heat.getOrElse(Fire5).temp <= safetyTemp-dTempMax*2)

    // 5) If we found, we read the position and transmit
    val transmitIfFound = if (rs.ns.person == Some(true)) {
      rt.tt == TFound
    } else {
      rt.tt == TRepeat || rt.tt == TIdle
    }

    forwardIfNotOutOfMap && freshSensors  && freshSensors2 && forwardIfNoWall && forwardIfNotHot && transmitIfFound
  }

  def validWorld(implicit w: World): Boolean = {
    val dim = w.dimentions

    dim.x > 0 && dim.y > 0 && dim == w.rs.es.dim &&
    w.isWithinMap(w.rs.es.pos) &&
    w.clock >= 0
  }

  def validState(rs: RobotState)(implicit w: World): Boolean = {
    
    // 6) Sensors have consistent data
    val recentData = rs.ns.validData && rs.hs.validData

    // 2/3) We don't end up in a wall
    val notInWall = !w.wallAt(rs.es.pos)

    // 2) We are in the map
    val inMap = w.isWithinMap(rs.es.pos)

    validWorld && recentData && notInWall && inMap
  }

  def validRobotStep(from: RobotState, to: RobotState)(implicit w: World): Boolean = {
    val posFrom      = from.es.pos
    val posFromFront = from.es.pos + from.es.orient
    val posTo        = to.es.pos
    val posToFront   = to.es.pos +to.es.orient

    // 1) Robot must not rotate and move at the same time
    val dontRotateAndMove = (from.es.pos == to.es.pos) || (from.es.orient == to.es.orient)

    // 4) We don't move to a cell that is too hot
    val dontBeCrazy = (posFrom == posTo) || (w.fireAt(posTo).temp <= safetyTemp)

    // 5) If we found somebody, we record its position for transmission
    val transmitWhenFound = (from.ns.person != Some(true)) || (to.ts.beacon == Some(posFromFront))

    dontRotateAndMove && dontBeCrazy && transmitWhenFound
  }

  def filterValid(rs: RobotState, rts: List[RobotTransition]): List[RobotTransition] = (rts match {
    case Cons(rt, rtt) =>
      val ts = filterValid(rs, rtt)

      if (validTransition(rs, rt)) {
        Cons(rt, ts)
      } else {
        ts
      }
    case Nil() => Nil[RobotTransition]()
  }) ensuring {
    res => allValid(rs, res)
  }

  def allValid(rs: RobotState, rts: List[RobotTransition]): Boolean = rts match {
    case Cons(rt, rtt) => validTransition(rs, rt) && allValid(rs, rtt)
    case Nil() => true
  }

  def worldStep(w: World): World = {
    World(w.clock + 1, w.dimentions, w.walls, w.persons, w.initFires, w.rs)
  } ensuring {
    w2 =>
      w.fireAt(w2.rs.es.pos).level <= w2.fireAt(w2.rs.es.pos).level &&
      w2.fireAt(w2.rs.es.pos).level <= w.fireAt(w2.rs.es.pos).level+1
  }

  def fireEvolution(from: FireLevel, to: FireLevel): Boolean = {
    (from.temp <= to.temp) &&
    (to.temp <= from.temp + dTempMax)
  }

  def searchAlgorithm(rs: RobotState): EngineTransition = {
    // Make a suggestion based on whatever kwnoledge you have, here we favor going forward
    EForward
  }

  def getBestTransition(rs: RobotState, ls: List[RobotTransition]): Option[RobotTransition] = {
    require(allValid(rs, ls))

    if (ls.isEmpty) {
      None[RobotTransition]()
    } else {
      val sugg = searchAlgorithm(rs)

      ls.find(rt => (rt.et == sugg) && validTransition(rs, rt)).orElse {
        Some(ls.head)
      }
    }
  } ensuring {
    res => res match {
      case Some(t) =>
        (ls.content contains t) && validTransition(rs, t)
      case None() =>
        ls.isEmpty
    }
  }

  def step(rs: RobotState)(implicit w: World) = {
    require(validState(rs) && w.rs == rs)

    val transitions = robotSucc(rs)

    val ort = getBestTransition(rs, transitions)

    val nextRs = ort match {
      case Some(rt) =>
        robotStep(rs, rt)

      case None() =>
        rs
    }

    (nextRs, ort)
  } ensuring {
    res =>
      val (rs2, ort) = res;
      validState(rs2) &&
      (ort match {
        case Some(rt) =>
          validRobotStep(rs, rs2)
        case None() =>
          true

      })
  }

  def globalSafe(implicit w: World): World = {
    require(validState(w.rs))

    // One step for the robot
    val (rs2, otr) = step(w.rs)

    // One step for mankind
    worldStep(World(w.clock, w.dimentions, w.walls, w.persons, w.initFires, rs2))
  } ensuring {
    w2 =>
      val heatOk = if (w.rs.es.pos == w2.rs.es.pos) {
        true
      } else {
        w2.fireAt(w2.rs.es.pos).temp <= safetyTemp
      }

      // 2/3) We don't end up in a wall
      val notInWall = !w2.wallAt(w2.rs.es.pos)

      // 2) We are in the map
      val inMap = w2.isWithinMap(w2.rs.es.pos)

      heatOk && notInWall && inMap
  }


  def main(a: Array[String]): Unit = {
    val map0 = """|XXXXXXXXX
                  |XR FF   X
                  |X    PXXXX
                  |XXX F  F X
                  |X    X   X
                  |XX FPXXXXX
                  |XXXXXX""".stripMargin

    val map1 = """|XXXXXXXXXXXXX
                  |X        R  X
                  |XP   X      X
                  |X    X      X
                  |X  XXXXXXX  X
                  |X   PX      X
                  |X    X      X
                  |XFF  X      X
                  |XXXXXXXXXXXXX""".stripMargin

    var initPos: Position = Position(0, 0)

    var walls   = Set[Position]()
    var mission = Set[Position]()
    var persons = Set[Position]()
    var fires   = Set[Position]()

    for ((line, y) <- map1.split("\n").toSeq.zipWithIndex;
         (c, x) <- line.zipWithIndex) {

      val p = Position(x, y)

      c match {
        case 'R' =>
          initPos = p

        case 'X' =>
          walls += p

        case 'F' =>
          fires += p

        case 'P' =>
          persons += p

        case ' ' =>
      }

      if (c != 'X') {
        mission += p
      }
    }


    val dim = Position(walls.theSet.map(_.x).max+1, walls.theSet.map(_.y).max+1)

    val es  = EngineState(initPos, dim, North)
    val ns = NavSensorState(None(), None())
    val hs = HeatSensorState(None())
    val t  = TransmitterState(None())

    val rs = RobotState(es, ns, hs, t)

    implicit var w = World(0, dim, walls, persons, fires, rs)

    while(w.clock < 110) {
      print("\u001b[2J")
      val (rs2, otr) = step(w.rs)
      w = w.copy(rs = rs2)
      w = worldStep(w)
      draw(w, otr)
      Thread.sleep(120l)
    }
  }

  @ignore
  def draw(w: World, ogt: Option[RobotTransition]): Unit = {
    val rs = w.rs

    def navSens(ns: NavSensorState): String = {
      ns.wall.map(v => if (v) "X" else  "_").getOrElse("?")
    }

    val o = (rs.es.orient match {
      case North => "^"
      case East  => ">"
      case South => "v"
      case West  => "<"
    })+" "+rs.es.pos.x+","+rs.es.pos.y

    print("Last Action: ")
    ogt match {
      case Some(gt) =>
        println(s"E: ${gt.et}, NS: ${gt.nst}, HS: ${gt.hst}, T: ${gt.tt}")

      case None() =>
        println("<stuck>")
    }
    println()
    println(s"World Clock: ${w.clock}")
    println()
    println("Robot State: ")
    println(s" - Engine       : ${rs.es}")
    println(s" - Nav Sensor   : ${rs.ns}")
    println(s" - Heat Sensor  : ${rs.hs}")
    println(s" - Transmitter  : ${rs.ts}")

    println()
    println("Map:")
    println()

    val colors = List(52, 124, 1, 160, 196);

    for (y <- BigInt(0) until w.dimentions.y) {
      for(x <- BigInt(0) until w.dimentions.x) {

        val p = Position(x, y)

        val f = w.fireAt(p)
        if (f != NoFire) {
          val code = colors(f.level-1)
          print("\u001b[48;5;"+code+"m")
        }

        if (w.walls contains p) {
          print("\u2593")
        } else if (rs.es.pos == p) {
          print((rs.es.orient match {
            case North => "^"
            case South => "v"
            case East => ">"
            case West => "<"
          }))
        } else if (w.persons contains p) {
          print("P")
        } else {
          print(" ")
        }

        if (f != NoFire) {
          print(Console.RESET)
        }

      }
      println
    }
  }

  def ||(ets: List[EngineTransition],
         nsts: List[NavSensorTransition],
         hsts: List[HeatSensorTransition],
         tts: List[TransmitterTransition]): List[RobotTransition] = {

    ets.flatMap { et =>
      nsts.flatMap { nst =>
        hsts.flatMap { hst =>
          tts.map { tt =>
            RobotTransition(et, nst, hst, tt)
          }
        }
      }
    }
  }
}
