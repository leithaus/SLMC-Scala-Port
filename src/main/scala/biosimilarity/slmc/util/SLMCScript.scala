package biosimilarity.slmc.util

import scala.collection.SeqProxy
import biosimilarity.slmc.ast.ss.SLMCStatement
import biosimilarity.slmc.ast.parsing.Parser
import java.io.PrintWriter
import java.io.FileOutputStream
import biosimilarity.slmc.Evaluator
import biosimilarity.slmc.SLMC

class SLMCScript(val history: Seq[SLMCStatement]) extends SeqProxy[SLMCStatement] with Showable {
	def self = history

  def this(file: String) = this(Parser.fromFile(file).toSeq)
  
  def evaluate(environment: SLMC): (SLMC, String) = {
	  val logger = new Logger
	  var env = environment
	  for(command <- self) {
	    val (newEnv, response) = Evaluator(env, command)
	    env = newEnv
	    logger.logln(response.msg)
	  }
	  (env, logger.getLog)
	}
  
  def save(filename: String): Boolean = {
	  try {
	  	val out = new PrintWriter(new FileOutputStream(filename))
	  	out.print(show())
	  	true
	  } catch { case _: Throwable => false }
	}
	
	def show(): String = {
	  val logger = new Logger
	  for(command <- self) {
	    logger.logln(command.show)
	  }
	  logger.getLog
	}
}

object SLMCScript {
  
  def fromString(s: String): SLMCScript = {
    new SLMCScript(Parser.fromString(s).toSeq)
  }
  
}