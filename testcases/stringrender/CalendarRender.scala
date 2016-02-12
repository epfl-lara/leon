import leon.lang._
import leon.lang.synthesis._
import leon.annotation._
import leon.collection._

object CalendartoString {
  val dayEventsSep = "\n"
  val eventsSep = "\n"
  val daysSep = "\n\n"  
  val hoursSep = "-"
  val dayPlusPrefix = " (D+"
  val dayPlusSuffix = ")"
  val hoursDescriptionSep = " : "
  val titleDescriptionSep = "\n"
  
  case class Week(days: List[Day])
  case class Day(name: String, events: List[Event])
  case class Event(startHour: Int, startMinute: Int, durationMinutes: Int, description: String)
  
  def renderHour(h: Int, m: Int) = {
    //require(m >= 0 && m < 60 && h > 0)
    val h_adjusted = h + m / 60
    val realh = h_adjusted  % 24 
    val realm = m % 60
    val days = h_adjusted / 24 
    realh + "h" + (if(realm == 0) "" else (if(realm < 10) "0" + realm else realm.toString)) + (if(days > 0) dayPlusPrefix + days + dayPlusSuffix else "")
  }
  
  def renderEvent(e: Event) = {
    renderHour(e.startHour, e.startMinute) + hoursSep + renderHour(e.startHour, e.startMinute + e.durationMinutes) + hoursDescriptionSep + e.description
  }
  
  def renderList[T](l: List[T], f: T => String, prefix: String, separator: String, suffix: String): String = l match {
    case Nil() => prefix + suffix
    case Cons(e, tail:Cons[T]) => prefix + f(e) + separator + renderList(tail, f, "", separator, suffix)
    case Cons(e, Nil()) => prefix + f(e) + suffix
  }
  
  def renderDay(d: Day): String = {
    renderList(d.events, (e: Event) => renderEvent(e), d.name + dayEventsSep, eventsSep, "")
  }
  
  def renderWeek(s: Week): String = {
    renderList(s.days, (d: Day) => renderDay(d), """Dear manager,
Here is what happened last week:
""", daysSep, "")
  } ensuring { (res: String) => 
    (s, res) passes {
      case Week(Cons(Day("Wednesday", Cons(Event(8, 30, 60, "First meeting"), Cons(Event(23, 15, 420, "Bus journey"), Nil()))), Cons(Day("Thursday", Cons(Event(12, 0, 65, "Meal with client"), Nil())), Nil()))) => """Dear manager,
Here is what happened last week:
Wednesday
8h30-9h30 : First meeting
23h15-6h15 (D+1) : Bus journey

Thursday
12h-13h05 : Meal with client"""
    }
  }
}