@spec object UISpecs {
  sealed abstract class UIWidget
  case class Widget extends UIWidget(kind : WidgetKind, contents : OptionString, reference : OptionUIRef, handlers : HandlerList, layoutElems : StyleClassList, subwidgets : UIWidgetList)
  
  // no constructors, just abstract type:
  sealed abstract class UIRef

  // also an abstraction, the environment (mapping of widget references to contents):
  sealed abstract class UIEnv

  // how do we store this function?
  sealed abstract class CommandAbs
  case class Command(function : UIEnv => Unit) extends CommandAbs

  sealed abstract class HandlerAbs
  case class Handler(event : Event, command : Command) extends HandlerAbs

  sealed abstract class Event
  case class DefaultEvent() extends Event
  case class FocusIn() extends Event
  case class FocusOut() extends Event
  case class MouseButton1() extends Event
  case class MouseButton2() extends Event
  case class MouseButton3() extends Event
  case class KeyPress() extends Event
  case class Return() extends Event
  case class Change() extends Event
  case class DoubleClick() extends Event

  sealed abstract class WidgetKind
  case class Col() extends WidgetKind
  case class Row() extends WidgetKind
  case class Label() extends WidgetKind
  case class Button() extends WidgetKind
  case class Entry() extends WidgetKind
  case class TextEdit(height : Int, width : Int) extends WidgetKind
  // ...

  def col(ws : UIWidgetList) : UIWidget =
    Widget(Col(), NoneString(), NoneUIRef(), NilHandler(), NilStyleClass(), ws)

  def row(ws : UIWidgetList) : UIWidget =
    Widget(Row(), NoneString(), NoneUIRef(), NilHandler(), NilStyleClass(), ws)

  def label(str : String) : UIWidget =
    Widget(Label(), SomeString(str), NoneUIRef(), NilHandler(), NilStyleClass(), NilUIWidget())
  
  // ...
}
