package biosimilarity.slmc.ast.cc

import biosimilarity.slmc.util.Showable

sealed abstract class ConversationCalculus extends ConversationCalculusLike
case object Inaction extends ConversationCalculus
case class Parallel(ast: ConversationCalculus, ast2: ConversationCalculus) extends ConversationCalculus
case class Sum(ast: List[ConversationCalculus]) extends ConversationCalculus
case class Context(conv: String, ast: ConversationCalculus) extends ConversationCalculus
case class This(thisVar: String, ast: ConversationCalculus) extends ConversationCalculus
case class Action(action: ActionType, ast: ConversationCalculus) extends ConversationCalculus
case class Definition(label: String, ast: ConversationCalculus) extends ConversationCalculus
case class New(conv: String, label: String, ast: ConversationCalculus) extends ConversationCalculus
case class Join(conv: String, label: String, ast: ConversationCalculus) extends ConversationCalculus
case class Variable(name: String, arguments: List[String]) extends ConversationCalculus
case class IfThenElse(astt: ConversationCalculus, astf: ConversationCalculus) extends ConversationCalculus

sealed abstract class Direction
case object Here extends Direction
case object Up extends Direction

sealed abstract class ActionType extends ActionLike
case class Input(direction: Direction, label: String, args: List[String]) extends ActionType
case class Output(direction: Direction, label: String, args: List[String]) extends ActionType

trait ConversationCalculusLike extends Showable { 
  def show(): String = {
    this match {
      case Inaction => 
        "end"
      case Parallel(left, right) => 
        "(%s\n | \n%s)".format(left.show, right.show)
      case Sum(asts) => 
        "switch {\n%s}\n".format(intercalate("")(asts.map(_.show)))
      case Context(conv, ast) =>
        "context " + conv + " {\n" + ast.show + "} "
      case This(thisvar, ast) =>
        "this(" + thisvar + ").\n" + ast.show
      case Action(action, ast) =>
        "%s\n%s".format(action.show, ast.show)
      case Definition(label, ast) =>
        "def %s => (\n%s)".format(label, ast.show)
      case New(conv,label,ast) =>
        "new %s.%s <= (\n%s)".format(conv, label, ast.show)
      case Join(conv,label,ast) =>
        "join %s.%s <= (\n%s)".format(conv, label, ast.show)
      case Variable(rvar,ids) =>
        "%s(%s)".format(rvar, intercalate(",")(ids))
      case IfThenElse(astt,aste) =>
        "if (cond) then \n%s\nelse \n%s".format(astt.show, aste.show)
    }
  }
}

trait ActionLike extends Showable {
  def show() =
    this match {
      case Input(direction, label, args) =>
        if(direction == Here) {
          label + "?(" + intercalate(",")(args) + ")."
        } else {
          label + "^?(" + intercalate(",")(args) + ")."
        }
      case Output(direction, label, args) =>
        if(direction == Here) {
          label + "!(" + intercalate(",")(args) + ")."
        } else {
          label + "^!(" + intercalate(",")(args) + ")."
        }
    }
}