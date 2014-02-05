package biosimilarity.slmc

import ast.ss._
import biosimilarity.slmc.ast.sr._
import scala.collection.immutable
import biosimilarity.slmc.util.OCaml.Ref
import biosimilarity.slmc.ast.parsing.Parser
import biosimilarity.slmc.util.DebugServer

object Main {
  
  var env = new SLMC
  var pwd = System.getProperty("user.dir")
  
  def main(args: Array[String]) {
    if(Array(args).contains("-server")) {
      DebugServer.setPersistence(Array(args).contains("-persist"))
      DebugServer.start()
    } else if(args.length == 2) {
      for(command <- Parser.fromFile(args(1))) {
        val (newEnv, response) = Evaluator(env, command)
        env = newEnv
        println(response.msg)
      }
    } else {
      for(command <- Parser.fromStdin()) {
        val (newEnv, response) = Evaluator(env, command)
        env = newEnv
        println(response.msg)
      }
    }
  }

}