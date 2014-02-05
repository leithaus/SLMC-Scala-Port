package biosimilarity.slmc.ast.parsing

import biosimilarity.slmc.ast.ss.SLMCStatement
import biosimilarity.slmc.ast.ss.Done
import java.io.FileInputStream
import java.io.StringReader
import java.io.InputStream

class Parser(private val parser: ParserCup) extends Iterator[SLMCStatement] {
  
  var nextStatement: SLMCStatement = parser.parse().value.asInstanceOf
  
  override def hasNext() = 
  	next match {
      case Done => false
      case _ => true
    }
  
  override def next(): SLMCStatement = {
    val res = next
    nextStatement = parser.parse().value.asInstanceOf
	  res
  }

}

object Parser {
  
  def fromStdin(): Parser = {
    val lexer = new Lexer(Console.in)
    val parser = new ParserCup(lexer)
    new Parser(parser)
  }
  
  def fromFile(file: String): Parser = {
    val input = new FileInputStream(file)
  	val lexer = new Lexer(input)
    val parser = new ParserCup(lexer)
    new Parser(parser)
  }
  
  def fromInputStream(stream: InputStream): Parser = {
    val lexer = new Lexer(stream)
    val parser = new ParserCup(lexer)
    new Parser(parser)
  }
  
  def fromString(string: String): Parser = {
    val input = new StringReader(string)
    val lexer = new Lexer(input)
    val parser = new ParserCup(lexer)
    new Parser(parser)
  }
  
}