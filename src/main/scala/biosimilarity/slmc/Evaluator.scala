package biosimilarity.slmc

import biosimilarity.slmc.ast.ss._
import biosimilarity.slmc.ast.sr._
import biosimilarity.slmc.ast.parsing.ParserCup
import java.io.FileInputStream
import biosimilarity.slmc.ast.parsing.Lexer
import biosimilarity.slmc.ast.parsing.Parser

object Evaluator {
  
  val checker = new Checker()
  var pwd = System.getProperty("user.dir")
  
  def apply(environment: SLMC, statement: SLMCStatement): (SLMC, SLMCResponse) = {
    var env = environment
    val response: SLMCResponse = 
      try {
			  statement match {
			    case Clear =>
			      env = new SLMC
			      OK("clear")
			    case Done =>
			      OK("")
			    case Help =>
			      OK("\n- Listing commands -\n"
			      + "\ndefproc ID[(n1,...)] = <process> (and ID[(n1,...)] = <process>)*;"
			      + "\ndefprop id[(n1,...,P1,...)] = <formula>;"
			      + "\ncheck <process id> [(n1,...)] |= <formula>;"
			      + "\nparameter [<parameter id> [new_value]];"
			      + "\nlist [procs | props];\nshow [id | ID];\nload \"<filename>\";"
			      + "\ncd \"<pathname>\";\npd;"
			      + "\ntrace [on | off];\nclear;\nhelp;\nquit;\n\n")
			    case ListParameters =>
			      OK("\n- Listing parameters -\n\nmax_threads\nshow_time\ncheck_counter\n\n")
			    case Pass =>
			      OK("...")
			    case PrintCheckCounter =>
			      if (checker.showCheckCounter)
			        OK("- Parameter check_counter is on -")
			      else
			        OK("- Parameter check_counter is off -")
			    case PrintDirectory =>
			      OK(pwd)
			    case PrintMaxThreads =>
			      OK("- Current value for max_threads is " + checker.maxThreads)
			    case PrintProcesses =>
			      OK(env.showProcesses())
			    case PrintPropositions =>
			      OK(env.showPropositions())
			    case PrintShowTime =>
			      if(checker.showTime)
			        OK("- Parameter show_time is on -")
			      else
			        OK("- Parameter show_time is off -")
			    case PrintTrace =>
			      if (checker.showTrace)
			        OK("- Trace option is on -")
			      else
			        OK("- Trace option is off -")
			    case Check(name, arguments, proposition) =>
			      val (pass, response) = checker.check(env, name, arguments, proposition)
			      CheckComplete(pass, response)
			    case DefineMaxThreads(max) =>
			      checker.maxThreads = max
			      Evaluator(env, PrintMaxThreads)._2
			    case DefinePiProcesses(names, argumentss, definitions) =>
			      env = env.installPiProcesses(names, argumentss, definitions)
			      Evaluator(env, PrintProcesses)._2
			    case DefineCCProcess(name, arguments, definition) =>
			      env = env.installConversationCalculus(name, arguments, definition)
			      Evaluator(env, PrintProcesses)._2
			    case DefineProposition(name, parameters, propositions, definition) =>
			      env = env.installProposition(name, parameters, propositions, definition)
			      Evaluator(env, PrintPropositions)._2
			    case DefineCheckCounter(check) =>
			      checker.showCheckCounter = check
			      OK("Show Check Counter: " + check)
			    case DefineShowTime(showTime) =>
			      checker.showTime = showTime
			      OK("Show Time: " + showTime) 
			    case DefineTrace(showTrace) =>
			      checker.showTrace = showTrace
			      OK("Show Trace: " + showTrace) 
			    case ChangeDirectory(directory) =>
			      pwd = directory
			      OK(directory)
			    case Load(file) =>
				    try {
			      	for(command <- Parser.fromFile(file)) {
				        val (newEnv, _) = Evaluator(env, command)
				        env = newEnv
				      }
				      OK("")
			      } catch {
			        case _: Throwable => Fail("Syntax error")
			      }
			    case ShowProcess(process) =>
			      OK(env.showProcess(process))
			    case ShowProposition(proposition) =>
			      OK(env.showProposition(proposition))
			}
    } catch {
      case error: SLMCResponse => error
      case other: Throwable => Fail(other.getMessage())
    }
    (env, response)
  }
}