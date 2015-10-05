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
  case object Replace extends Action
  case object Erase extends Action
  case class Content(l: List[Int]) extends Action

  @extern
  def getCommand(): List[Int] = {
    print("> ")
    readLine().toList.map(_.toInt)
  }

  @extern
  def getOracle(): Oracle[Action] = {
    new KeyboardOracle()
  }

  def replStep(state: State): State = {
    if (state.mode == Quitted) {
      state
    } else {
      implicit val o = getOracle()
      val a = {
      //val a = withOracle { implicit o: Oracle[Action] =>
        val i = getCommand()

        getAction(i, state)
      }

      val newState = doAction(state, a)
      replStep(newState)
    }
  }

  @extern
  def unknown() = {
    println("?")
  }

  @extern
  def display(a: Action, s: State) = {
    println("  | Action : "+a)
    println("  | Line   : "+s.line)
    println("  | Curs   : "+s.cursor)
    println("  | Buff   : "+s.buffer)
    println("  | A*     : "+s.actions.map(_.toString).mkString(", "))
  }

  def getAction(input: List[Int], state: State)(implicit o: Oracle[Action]): Action = {
    ???
  }

  def doAction(state: State, action: Action): State = {
    val c = state.cursor
    val l = state.line

    val tmp = display(action, state)

    val ns = (action, state.actions) match {
      case (Content(cnt), Cons(Write, _)) =>
        val nl = l.take(c) ++ cnt ++ l.drop(c)
        state.setLine(nl).setCursor(c + cnt.size)
      case (Content(cnt), Cons(Replace, _)) =>
        val nl = l.take(c) ++ cnt ++ l.drop(c+cnt.size)
        state.setLine(nl).setCursor(c + cnt.size)
      case (Erase, _) =>
        state.setLine(Nil()).setCursor(0)
      case (Quit, _) =>
        state.setMode(Quitted)
      case _ =>
        unknown()
        state
    }

    ns.addAction(action)
  }

  @ignore
  @extern
  class KeyboardOracle[T: TypeTag](lvl: Int = 0) extends Oracle[T] {
    var result: T = _

    val ind = "  "*lvl

    lazy val h: T = {
      val m = runtimeMirror(getClass.getClassLoader)
      val oracleClass = typeOf[KeyboardOracle[T]].typeSymbol.asClass
      val refOracle   = m.reflectClass(oracleClass)

      val ls = Erase

      val tpeClass = typeOf[T].typeSymbol.asClass
      println(s"~${ind} Requesting value for (_ <: ${typeOf[T]}):")

      var askAgain = true
      while (askAgain) {
        if (tpeClass.isSealed) {
          val TypeRef(pre, sym, tpts) = typeOf[T]
          val subClasses = tpeClass.knownDirectSubclasses.toSeq.sortBy(_.name.toString)

          for ((sub, i) <- subClasses.zipWithIndex) {
            println(f"~${ind}  $i%2d: $sub%s")
          }

          print(s"~${ind} > ")
          val i = readLine().toInt
          if (i >= 0 && i < subClasses.size) {
            val subClass = subClasses(i).asClass
            val subType  = TypeRef(pre, subClass, tpts)

            val refClass = m.reflectClass(subClass)
            val ctor     = subType.declaration(nme.CONSTRUCTOR).asMethod
            val refCtor  = refClass.reflectConstructor(ctor)
            val ctorTpe  = ctor.typeSignatureIn(subType).asInstanceOf[MethodType]

            val rargs = for (arg <- ctorTpe.params) yield {
              val argTpe        = arg.typeSignature
              val oracleTpe     = typeRef(NoPrefix, oracleClass, List(argTpe))
              val oracleCtor    = oracleTpe.declaration(nme.CONSTRUCTOR).asMethod
              val refOracleCtor = refOracle.reflectConstructor(oracleCtor)

              val typeTag = TypeTag(m, new TypeCreator {
                def apply[U <: Universe with Singleton](m: Mirror[U]): U#Type = {
                  if (m == runtimeMirror(getClass.getClassLoader)) {
                    argTpe.asInstanceOf[U#Type]
                  } else {
                    sys.error("Unsupported")
                  }
                }
              })

              // Build an instance of this oracle:
              val oracle = refOracleCtor(lvl+1, typeTag)

              // We call its `head` method
              val head = oracleTpe.declaration(("head": TermName)).asMethod

              m.reflect(oracle).reflectMethod(head)()
            }

            result = refCtor(rargs: _*).asInstanceOf[T]
            askAgain = false;
          }
        } else if (tpeClass.name.toString == "Int") {
          print(s"~${ind} > ")
          try {
            result = readLine().toInt.asInstanceOf[T]
            askAgain = false
          } catch {
            case _: Throwable =>
          }
        } else if (tpeClass.name.toString == "Boolean") {
          print(s"~${ind} > ")
          readLine() match {
            case "true" =>
              result = true.asInstanceOf[T]
              askAgain = false
            case "false" =>
              result = false.asInstanceOf[T]
              askAgain = false
            case _ =>
          }
        } else {
          sys.error("Don't know how to generate for non-sealed class")
        }
      }

      result
    }


    lazy val l = new KeyboardOracle[T]()
    lazy val r = new KeyboardOracle[T]()
    override def head  = h
    override def left  = l
    override def right = r
  }

  def repl() = {
    val state = State(Nil(), 0, Nil(), Nil(), Edit)
    replStep(state)
  }

  @ignore
  @extern
  implicit def scalaToList[T](l: ScalaList[T]): List[T] = {
    l.foldLeft[List[T]](Nil())( (l, e) => Cons(e, l) )
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


}
