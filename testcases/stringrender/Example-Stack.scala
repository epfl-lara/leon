import leon.collection._
import leon.collection.List
import leon.lang._
import leon.proof.check
import leon.lang.synthesis._
import scala.language.postfixOps


/** The Concurrency object defines the semantics of concurrent programs.
  *
  * It gives the definition of libraries, and gives a function 
  * isLibraryExecution which describes valid executions of the library.
  * We show the files AtomicStack and TreiberStack how to instantiate it in 
  * order to describe specific implementations.
  */



object Concurrency {
  
  /** The class Method gives a syntax to define a method of a library.
    *
    * A Method is a tuple (initials,transitions,finals) where:
    * "initials" gives the initial state of the method depending on the argument
    * "transitions" in transition relation, which specifies how local and global
    * states are updated
    * "finals" gives the final states, and the corresponding return value 
    *   a state mapped to None means it's not final and the method cannot return here
    *
    * ArgData is the type of arguments values, given to the method
    * RetData is the type of the values returned by the method
    * LocalState is the type representing the local variables and control-flow positions
    *   of the method
    */
    
  case class Method[ArgData,RetData,LocalState,GlobalState](
    initials: ArgData => LocalState,
    transitions: (LocalState,GlobalState) => (LocalState,GlobalState),
    finals: LocalState => Option[RetData]
  )
  
  
  /** A Library associates to each method name a Method instance */
  
  case class Library[MethodName,ArgData,RetData,LocalState,GlobalState](
    methods: MethodName => Method[ArgData,RetData,LocalState,GlobalState]
  )
  
  
  /** The Event class represents low-level events.
    *
    * Each event is executed by a particular thread (type Tid).
    
    * An event can be a call event. In which case, the event has information
    * about the method `m' called, and the argument `arg' with which m was 
    * called.
    *
    * An event can be a return event. In which case, the event the same 
    * information than the corresponding call event, plus the return 
    * value `rv' (in RetData) which was returned.
    *
    * Otherwise, an event is an internal event (inside a method).
    */
  
  abstract class Event[Tid,MethodName,ArgData,RetData]
  case class CallEvent[Tid,MethodName,ArgData,RetData]
    (tid: Tid, m: MethodName, arg: ArgData) extends Event[Tid,MethodName,ArgData,RetData]
  case class RetEvent[Tid,MethodName,ArgData,RetData]
    (tid: Tid, m: MethodName, arg: ArgData, rv: RetData) extends Event[Tid,MethodName,ArgData,RetData]
  case class InternalEvent[Tid,MethodName,ArgData,RetData]
    (tid: Tid) extends Event[Tid,MethodName,ArgData,RetData]
  
  
  
  /** The Configuration class describes the whole state of a concurrent system.
    *
    * More precisely, it is a pair composed of a global state, and a map giving
    * for each thread, the local state of the method in which the thread is.
    * The map also stores information about the method name and the argument 
    * value with which the method was called.
    * A thread mapped to None means that the thread is not currently calling 
    * any method.
    *
    * Intuitively, the global state represents the valuation of the global
    * variables which are shared between the different methods. For programs 
    * which can use memory allocation, it should also represent the heap.
    */
 
  case class Configuration[Tid,MethodName,ArgData,LocalState,GlobalState](
    gs: GlobalState, 
    control: List[(Tid,Option[(MethodName,ArgData,LocalState)])]
  )
  
  
  /** This class describes client's of a library.
    *
    * A client can be composed of multiple thread. It specifies for each 
    * thread, the sequence of calls made to the library, with the expected*
    * return values.
    */
  
  case class Client[Tid,MethodName,ArgData,RetData](threads: Tid => List[Event[Tid,MethodName,ArgData,RetData]])
}

object AtomicStack {

  import Concurrency._
  
  
  
  /** Represents the states of the control-flow graph of the push and pop 
    * methods.
    */
  
  abstract class StackState
  case class ValueState(v: BigInt) extends StackState 
  case class EmptyState() extends StackState
  case class InitState() extends StackState
  case class FinalState() extends StackState
  case class BlockState() extends StackState
  
  
  abstract class StackTid
  case class T1() extends StackTid
  case class T2() extends StackTid
  
  
  /** We now describe the Atomic Stack library.
    *
    * The arguments taken by push and pop are of type Option[BigInt].
    * Typically the pop method won't take an argument (None), while 
    * push will take a BigInt argument (Some[BigInt]).
    *
    * Similarly, the type of return values is also Option[BigInt].
    *
    */
  
  def initialsPush(arg: Option[BigInt]): StackState = arg match {
    case None() => BlockState()
    case Some(arg) => ValueState(arg)
  }
  
  def transitionsPush(ls: StackState, gs: List[BigInt]): (StackState,List[BigInt]) = (ls,gs) match {
    case (ValueState(arg),_) => (FinalState(), arg :: gs)
    case _ => (BlockState(), gs)
  }
  
  def finalsPush(ls: StackState): Option[Option[BigInt]] = ls match {
    case FinalState() => Some(None())
    case _ => None()
  }
  
  val PushMethod: Method[Option[BigInt],Option[BigInt],StackState,List[BigInt]] = {
    Method(initialsPush,transitionsPush,finalsPush)
  }
  
  
  def initialsPop(arg: Option[BigInt]): StackState = InitState()
  
  def transitionsPop(ls: StackState, gs: List[BigInt]): (StackState,List[BigInt]) = (ls,gs) match {
      case (InitState(),Nil()) => (EmptyState(), Nil())
      case (InitState(),Cons(rv,rvs)) => (ValueState(rv),rvs)
      case _ => (BlockState(), gs)
  }
  
  def finalsPop(ls: StackState): Option[Option[BigInt]] = ls match {
      case EmptyState() => Some(None())
      case ValueState(arg) => Some(Some(arg))
      case _ => None()
  }
  
  val PopMethod: Method[Option[BigInt],Option[BigInt],StackState,List[BigInt]] = {
    Method(initialsPop,transitionsPop,finalsPop)
  }

  abstract class StackMethodName
  case class Push() extends StackMethodName
  case class Pop() extends StackMethodName
  
  
  def methods(name: StackMethodName): Method[Option[BigInt],Option[BigInt],StackState,List[BigInt]] = name match {
    case Push() => PushMethod  
    case Pop() => PopMethod  
  }
  
  val libAtomicStack = Library[StackMethodName,Option[BigInt],Option[BigInt],StackState,List[BigInt]](methods)

  
  def threads(tid: StackTid): List[Event[StackTid,StackMethodName,Option[BigInt],Option[BigInt]]] = tid match {
    case T1() => 
      List(
        CallEvent(T1(),Push(),Some(5)),
        RetEvent(T1(),Push(),Some(5),None())
      )
    case T2() => 
      List(
        CallEvent(T2(),Pop(),None()),
        RetEvent(T2(),Pop(),None(),Some(5))
      )
  }
  
  val client: Client[StackTid,StackMethodName,Option[BigInt],Option[BigInt]] = Client(threads)
  
  def threadToStringSimplest(p: StackTid): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case T1()
      =>
     "T1: call Push(5)"
    }
  }
  
  def threadToStringSimple0(p: Event[StackTid,StackMethodName,Option[BigInt],Option[BigInt]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case CallEvent(T1(), Push(), Some(BigInt(5)))
      =>
     "T1: call Push(5)"
    }
  }
  
  def threadToStringSimple1(p: List[Event[StackTid,StackMethodName,Option[BigInt],Option[BigInt]]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case Cons(CallEvent(T1(), Push(), Some(BigInt(5))),
           Cons(InternalEvent(T1()), Nil()))
      =>
     "T1: call Push(5)\nT1: internal"
    }
  }
  
  def threadToStringSimple2(p: List[Event[StackTid,StackMethodName,Option[BigInt],Option[BigInt]]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case Cons(RetEvent(T1(), Push(), Some(BigInt(5)), None()),
           Cons(InternalEvent(T2()),
           Cons(RetEvent(T2(), Pop(), None(), Some(BigInt(5))), Nil())))
      =>
     "T1: ret Push(5)\nT2: internal\nT2: ret Pop() -> 5"
    }
  }
  
  
  /** This is THE method we want to render */
  def threadToString(p: List[Event[StackTid,StackMethodName,Option[BigInt],Option[BigInt]]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case Cons(CallEvent(T1(), Push(), Some(BigInt(5))),
           Cons(InternalEvent(T1()),
           Cons(CallEvent(T2(), Pop(), None()),
           Cons(RetEvent(T1(), Push(), Some(BigInt(5)), None()),
           Cons(InternalEvent(T2()),
           Cons(RetEvent(T2(), Pop(), None(), Some(BigInt(5))), Nil()))))))
      =>
     "T1: call Push(5)\nT1: internal\nT2: call Pop()\nT1: ret Push(5)\nT2: internal\nT2: ret Pop() -> 5"
    }
  }
  
  // Warning: Spacing differs from records to records.
  // Warning: The displaying of a tuple might depend on its operands.
  def configurationToString(p: List[Configuration[StackTid, StackMethodName, Option[BigInt], StackState, List[BigInt]]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case Cons(Configuration(Nil(), Cons((T1(), Some((Push(), Some(BigInt(5)), ValueState(BigInt(5))))), Nil())),
           Cons(Configuration(Cons(BigInt(5), Nil()), Cons((T1(), Some((Push(), Some(BigInt(5)), FinalState()))), Nil())),
           Cons(Configuration(Cons(BigInt(5), Nil()), Cons((T2(), Some((Pop(), None(), InitState()))), Cons((T1(), Some((Push(), Some(BigInt(5)), FinalState()))), Nil()))),
           Cons(Configuration(Cons(BigInt(5), Nil()), Cons((T2(), Some((Pop(), None(), InitState()))), Cons((T1(), None()), Nil()))),
           Cons(Configuration(Nil(), Cons((T2(), Some((Pop(), None(), ValueState(BigInt(5))))), Cons((T1(), None()), Nil()))),
           Cons(Configuration(Nil(), Cons((T2(), None()), Cons((T1(), None()), Nil()))), Nil())))))) =>
      """([], { 
  T1 -> Push(5): ValueState(5) 
})


([5], { 
  T1 -> Push(5): FinalState 
})


([5], { 
  T2 -> Pop(): InitState; 
  T1 -> Push(5): FinalState 
})


([5], {
  T2 -> Pop(): InitState;
  T1 -> idle
})


([], {
  T2 -> Pop(): ValueState(5);
  T1 -> idle
})


([], {
  T2 -> idle;
  T1 -> idle
})"""

    }
  }
  /*
  /// Out of order configurationToString
  def configurationToStringOOO(p: List[Configuration[StackTid, StackMethodName, Option[BigInt], StackState, List[BigInt]]]): String = {
    ???[String]
  } ensuring {
    res => (p, res) passes {
      case Cons(Configuration(Nil(), Map(T1() -> Some((Push(), Some(BigInt(5)), ValueState(BigInt(5)))))),
           Cons(Configuration(Cons(BigInt(5), Nil()), Map(T1() -> Some((Push(), Some(BigInt(5)), FinalState())))),
           Cons(Configuration(Cons(BigInt(5), Nil()), Map(T2() -> Some((Pop(), None(), InitState())), T1() -> Some((Push(), Some(BigInt(5)), FinalState())))),
           Cons(Configuration(Cons(BigInt(5), Nil()), Map(T2() -> Some((Pop(), None(), InitState())), T1() -> None())),
           Cons(Configuration(Nil(), Map(T2() -> Some((Pop(), None(), ValueState(BigInt(5)))), T1() -> None())),
           Cons(Configuration(Nil(), Map(T2() -> None(), T1() -> None())), Nil())))))) =>
      """([], { 
  T1 -> ValueState(5) in Push(5)
})


([5], { 
  T1 -> FinalState in Push(5)
})


([5], { 
  T2 -> InitState in Pop(); 
  T1 -> FinalState in Push(5)
})


([5], {
  T2 -> InitState in Pop();
  T1 -> idle
})


([], {
  T2 -> ValueState(5) in Pop();
  T1 -> idle
})


([], {
  T2 -> idle;
  T1 -> idle
})"""

    }
  }*/
}

