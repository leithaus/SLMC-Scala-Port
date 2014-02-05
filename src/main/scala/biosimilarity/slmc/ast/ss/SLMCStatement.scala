package biosimilarity.slmc.ast.ss

import biosimilarity.slmc.ast.ml.ModalLogic
import biosimilarity.slmc.ast.pc.PiCalculus
import biosimilarity.slmc.ast.cc.ConversationCalculus
import biosimilarity.slmc.util.Showable

sealed abstract class SLMCStatement extends SLMCStatementLike
case object Clear extends SLMCStatement
case object Done extends SLMCStatement
case object Help extends SLMCStatement
case object ListParameters extends SLMCStatement
case object Pass extends SLMCStatement
case object PrintCheckCounter extends SLMCStatement
case object PrintDirectory extends SLMCStatement
case object PrintMaxThreads extends SLMCStatement
case object PrintProcesses extends SLMCStatement
case object PrintPropositions extends SLMCStatement
case object PrintShowTime extends SLMCStatement
case object PrintTrace extends SLMCStatement
case class ChangeDirectory(directory: String) extends SLMCStatement
case class Check(name: String, arguments: List[String], proposition: ModalLogic) extends SLMCStatement
case class DefineCCProcess(name: String, arguments: List[String], definition: ConversationCalculus) extends SLMCStatement
case class DefineCheckCounter(check: java.lang.Boolean) extends SLMCStatement
case class DefineMaxThreads(max: Integer) extends SLMCStatement
case class DefinePiProcesses(names: List[String], argumentss: List[List[String]], definitions: List[PiCalculus]) extends SLMCStatement
case class DefineProposition(name: String, parameters: List[String], propositions: List[String], definition: ModalLogic) extends SLMCStatement
case class DefineShowTime(showTime: java.lang.Boolean) extends SLMCStatement
case class DefineTrace(trace: java.lang.Boolean) extends SLMCStatement
case class Load(file: String) extends SLMCStatement
case class ShowProcess(process: String) extends SLMCStatement
case class ShowProposition(proposition: String) extends SLMCStatement

trait SLMCStatementLike extends Showable {
  
  def show(): String = {
    this match {
			case Clear =>
			  "clear;\n"
			case Done =>
			  "quit;\n"
			case Help =>
			  "help;\n"
			case ListParameters =>
			  "parameter;\n"
			case Pass =>
			  ";\n"
			case PrintCheckCounter =>
			  "param cc;\n"
			case PrintDirectory =>
			  "pd;\n"
			case PrintMaxThreads =>
			  "param max_threads;\n"
			case PrintProcesses =>
			  "list procs;\n"
			case PrintPropositions =>
			  "list props;\n"
			case PrintShowTime =>
			  "param show_time;\n"
			case PrintTrace =>
			  "trace;\n"
			case Check(name, VarArg(arguments), proposition: ModalLogic) =>
			  "check %s%s |= %s;\n".format(name, arguments, proposition.show)
			case DefineMaxThreads(max) =>
			  "parameter max_threads %d;\n".format(max)
			case DefinePiProcesses(names, argumentss, definitions) =>
			  val zipped = names.zip(argumentss).zip(definitions)
			  val processes = zipped.map({
			    case ((name, VarArg(arguments)), definition) =>
			      "%s%s = %s;\n".format(name, arguments, definition.show) })
			  processes match {
			    case Nil => ";\n"
			    case hd::tl =>
			      "defproc pi %s%s;\n".format(hd, tl.map("\nand "+ _))
			  }
			case DefineCCProcess(name, VarArg(arguments), definition) =>
			  "defproc cc %s%s = %s;\n".format(name, arguments, definition.show)
			case DefineProposition(name, parameters, propositions, definition) =>
			  "%s%s = %s;\n".format(name, VarArg.unapply(parameters ++ propositions).get, definition.show)
			case DefineCheckCounter(check) =>
			  "parameter check_counter %s;\n".format(check.toString())
			case DefineShowTime(showTime) =>
			  "parameter show_time %s;\n".format(showTime.toString())
			case DefineTrace(trace) =>
			  if(trace) {
			    "trace on;\n"
			  } else {
			    "trace off;\n"
			  }
			case ChangeDirectory(directory: String) =>
			  "cd \"%s\";\n".format(directory)
			case Load(file: String) =>
			  "load \"%s\";\n".format(file)
			case ShowProcess(process) =>
			  "show %s;\n".format(process)
			case ShowProposition(proposition) =>
			  "show %s;\n".format(proposition)
    }
  }
  
}