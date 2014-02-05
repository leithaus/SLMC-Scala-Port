package biosimilarity.slmc.data

import scala.collection.immutable.HashMap
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc._
import biosimilarity.slmc.util.Namegen._
import biosimilarity.slmc.ast.sr.UndeclaredIdentifier
import biosimilarity.slmc.ast.sr.Fail
import biosimilarity.slmc.ast.sr.WrongArgumentCount
  
  class NormalEquation(val restrictions: List[String],
      	  			       val actions: List[(PiCalculus, PiCalculus, List[String])],
      					       val sums: List[List[(PiCalculus, PiCalculus, List[String])]]) {
    
    def |(e: NormalEquation): NormalEquation = {
      new NormalEquation(restrictions ++ e.restrictions, actions ++ e.actions, sums ++ e.sums)
    }
    
    def +(e: NormalEquation): NormalEquation = {
      if(restrictions.length > 0 || e.restrictions.length > 0 || e.sums.length > 0) {
        throw Fail()
      } else if(sums.length == 1) {
        new NormalEquation(Nil, Nil, List(e.actions ++ sums.head))
      } else {
        new NormalEquation(Nil, Nil, List(e.actions ++ actions))
      }
    }
  }
  
  object NormalEquation {

    type Environment = Map[String, String]
    type GlobalEnvironment = Map[String, (List[String], PiCalculus)]
  
    def apply(environment: Environment,
        			globals: GlobalEnvironment,
        			names: List[String]): PiCalculus => NormalEquation = {
      def apply: PiCalculus => NormalEquation = {
				case Void =>
				  new NormalEquation(Nil, Nil, Nil)
				case Parallel(left, right) =>
				  apply(left) | apply(right)
				case Sum(left, right) =>
				  apply(left) + apply(right)
				case New(names, process) =>
				  val mapping = names.map((_, generateBoundName()))
				  val subEquation = NormalEquation(environment ++ mapping, globals, names ++ mapping.unzip._2)(process)
				  new NormalEquation(mapping.unzip._2 ++ subEquation.restrictions, subEquation.actions, subEquation.sums)
				case Action(pc.Input(channel, arguments), process) =>
				  val newChannel = environment.getOrElse(channel, channel)
				  val newArguments = arguments.map(n => environment.getOrElse(n, n))
				  val newProcess = if(process.isVoid(globals)) { Void } else { process.substitute(environment) }
				  val newAction = Action(pc.Output(newChannel, newArguments), newProcess)
				  new NormalEquation(Nil, List((newAction, process, names ++ newArguments)), Nil)
				case Action(pc.Output(channel, arguments), process) =>
				  val newChannel = environment.getOrElse(channel, channel)
				  val newArguments = arguments.map(n => environment.getOrElse(n, n))
				  val newProcess = if(process.isVoid(globals)) { Void } else { process.substitute(environment) }
				  val newAction = Action(pc.Input(newChannel, newArguments), newProcess)
				  new NormalEquation(Nil, List((newAction, process, names)), Nil)
				case Action(Tau, process) =>
				  val newProcess = if(process.isVoid(globals)) { Void } else { process.substitute(environment) }
				  val newAction = Action(Tau, newProcess)
				  new NormalEquation(Nil, List((newAction, process, names)), Nil)
				case Test(left, right, process, test) =>
				  val newLeft = environment.getOrElse(left, left)
				  val newRight = environment.getOrElse(right, right)
				  val newProcess = if(process.isVoid(globals)) { Void } else { process.substitute(environment) }
				  val newTest = Test(newLeft, newRight, newProcess, test)
				  new NormalEquation(Nil, List((newTest, process, names)), Nil)
				case Variable(name, arguments) =>
				  globals.get(name) match {
				    case None => throw UndeclaredIdentifier(name)
				    case Some((parameters, process)) =>
				      if(arguments.length != parameters.length)
				        throw WrongArgumentCount(name)
				      val argumentObjects = arguments.map(n => environment.getOrElse(n, n))
				      val subEnvironment = parameters.zip(argumentObjects).toMap
				      NormalEquation(subEnvironment, globals, names)(process)
				  }
      }
      apply
    }
  }