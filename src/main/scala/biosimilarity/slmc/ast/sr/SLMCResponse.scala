package biosimilarity.slmc.ast.sr

import biosimilarity.slmc.ast.ss.SLMCStatement
import scala.concurrent.duration.Duration

sealed abstract class SLMCResponse(val msg: String, val pass: Boolean = false) extends Exception(msg)
case class CheckComplete(override val pass: Boolean, override val msg: String = "") extends SLMCResponse(msg)
case class CheckerTimedOut(timeout: Duration) extends SLMCResponse("Checker timed out after " + timeout)
case class Fail(override val msg: String = "Failure") extends SLMCResponse(msg)
case object IllFormedAst extends SLMCResponse("Ill formed AST")
case object MaxThreads extends SLMCResponse("Max Threads")
case class OK(output: String, override val pass: Boolean = true) extends SLMCResponse(output)
case class ParseError(override val msg: String) extends SLMCResponse(msg)
case class UndeclaredIdentifier(id: String) extends SLMCResponse("Undeclared Identifier: " + id)
case class UnguardedRecursion(override val msg: String) extends SLMCResponse(msg)
case class WrongArgumentCount(name: String) extends SLMCResponse(name + ": Number of arguments and parameters differ!")
case class WrongArguments(override val msg: String) extends SLMCResponse(msg)
