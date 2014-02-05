package biosimilarity.slmc.data

import scala.collection.mutable
import scala.collection.immutable.HashMap
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc.{Test => _, Variable => _, _}
import biosimilarity.slmc.util.Namegen._
import Equation._
import NormalEquation.{Environment => _, _}
import biosimilarity.slmc.util.Monoid
import biosimilarity.slmc.util.Showable
import biosimilarity.slmc.util.Environment

class Equation(val parameterCount: Int,
               val restrictionCount: Int,
               val freeInputs: Actions,
               val freeOutputs: Actions,
               val boundInputs: Actions,
               val boundOutputs: Actions,
               val tests: Tests,
               val taus: Taus,
               val sums: Sums) extends Showable {
  def numFnOuts(): Int = { freeOutputs.length }
  def numBnOuts(): Int = { boundOutputs.length }
  def numFnInps(): Int = { freeInputs.length }
  def numBnInps(): Int = { boundInputs.length }
  def numTests():  Int = { tests.length }
  def numTaus():   Int = { taus.length }
    
  def actionCount: Int = {
    (numFnOuts + numFnInps
    + numBnOuts + numBnInps
    + numTests + numTaus + sums.length)
  }
  
  def allVariables: List[Variable] = {
    var variables: List[Variable] = Nil
    
    for((_, _, _, v, _) <- (freeOutputs ++ boundOutputs ++ freeInputs ++ boundInputs))
      variables ::= v
    
    for((_,_,_,v,_) <- tests)
      variables ::= v

    for((v,_) <- taus)
      variables ::= v
      
    for((actions, tests, taus) <- sums) {
	    for((_, _, _, v, _) <- actions)
	      variables ::= v
	    
	    for((_,_,_,v,_) <- tests)
	      variables ::= v
	
	    for((v,_) <- taus)
	      variables ::= v
    }
    variables
  }
  
  
  
  def show(): String = {
    var response = ""
      
    def showAction: Equation.Action => String = {
      case (t, sub, obj, v, args) =>
        var response = ""
        response += sub
        if(t == Equation.Output) {
          response += "!"
        } else {
          response += "?"
        }
        response += "(" + intercalate(",")(obj.map(_.show)) + ")."
        response += v + "(" + intercalate(",")(args.map(_.show)) + ")\n"
        response
    }
    
    def showTest: Equation.Test => String = {
      case (t, id1, id2, v, args) =>
        var response = ""
        response += "[" + id1.show
        if(t == Equals) {
          response += "="
        } else {
          response += "!="
        }
        response += id2.show + "]." + v
        response += "(" + intercalate(",")(args.map(_.show)) + ")\n"
        response
    }
    
    def showTau: Equation.Tau => String = {
      case (v, args) =>
        "tau." + v + "(" + intercalate(",")(args.map(_.show)) + ")\n"
    }
    
    def showSum: Equation.Sum => String = {
      case (acts, tests, taus) =>
        var response = ""
        response += intercalate("+ ")(acts.map(showAction(_)))
        if(acts.length > 0 && taus.length > 0 )
          response += "+ "
        response += intercalate("+ ")(taus.map(showTau(_)))
        if(acts.length + taus.length > 0 && tests.length > 0)
          response += "+ "
        response += intercalate("+ ")(tests.map(showTest(_)))
        response
    }
      
    response += "- #pars: " + parameterCount + "\n"
    response += "- #rests: " + restrictionCount + "\n"

    response += "- fnouts\n"
    for(fnout <- freeOutputs) {
      response += showAction(fnout)
    }

    response += "- bnouts\n"
    for(bnout <- boundOutputs) {
      response += showAction(bnout)
    }

    response += "- fninps:\n"
    for(fninp <- freeInputs) {
      response += showAction(fninp)
    }

    response += "- bninps:\n"
    for(bninp <- boundInputs) {
      response += showAction(bninp)
    }

    response += "- tests:\n"
    for(test <- tests) {
      response += showTest(test)
    }

    response += "- taus:\n"
    for(tau <- taus) {
      response += showTau(tau)
    }

    response += "- sums:\n"
    response += intercalate("\n")(sums.map(showSum(_)))
    response
  }
}
               
object Equation {
  
	sealed abstract class Name extends Showable {
	  def show: String = 
	  this match {
	    case Free(n) => s"Free($n)"
	    case Internal(i) => s"Internal($i)"
	    case Restricted(i) => s"Restricted($i)"
	    case Parameter(i) => s"Parameter($i)"
	  }
	}
	case class Free(n: String) extends Name
	case class Internal(i: Variable) extends Name
	case class Restricted(i: Variable) extends Name
	case class Parameter(i: Variable) extends Name
	
	sealed abstract class IO
	case object Output extends IO
	case object Input extends IO
  
  type Variable = Int
  type Names = List[Name]
  
  private type PreAction = (ml.Label, Variable, List[String])
  type Action = (IO, Name, Names, Variable, Names)
  type Actions = List[Action]
  
  private type PreTau = (Variable, List[String])
  type Tau = (Variable, Names)
  type Taus = List[Tau]
  
  private type PreTest = (TestType, String, String, Variable, List[String])
  type Test = (TestType, Name, Name, Variable, Names)
  type Tests = List[Test]
  
  
	type PreSum = (List[PreAction], List[PreTest], List[PreTau])
  type Sum = (Actions, Tests, Taus)
  type Sums = List[Sum]
  
  
  def apply(parameters: List[String],
            restrictions: List[String],
            actions: List[PreAction],
            tests: List[PreTest],
            taus: List[PreTau],
            sums: List[PreSum]): Equation = {
    val subEnvironment = new Environment[String, Name]()
    for((id, i) <- parameters.zipWithIndex) { subEnvironment.add(id, Parameter(i)) }
    for((id, i) <- restrictions.zipWithIndex) { subEnvironment.add(id, Restricted(i)) }
    val (freeInputs, boundInputs, freeOutputs, boundOutputs) = createActions(subEnvironment)(actions)
    val resTaus = createTaus(subEnvironment)(taus)
    val resTests = createTests(subEnvironment)(tests)
    val resSums = createSums(subEnvironment)(sums)
    new Equation(parameterCount = parameters.length,
                 restrictionCount = restrictions.length,
 						     freeOutputs = freeOutputs,
	 					     boundOutputs = boundOutputs,
		 				     freeInputs = freeInputs,
			 			     boundInputs = boundInputs,
				 		     tests = resTests,
					 	     taus = resTaus,
						     sums = resSums)
    
  }
	
	def nilEq(): Equation = {
	  new Equation(parameterCount = 0,
	  		         restrictionCount = 0,
	  		         freeInputs = Nil,
	  		         freeOutputs = Nil,
	  		         boundInputs = Nil,
	  		         boundOutputs = Nil,
	  		         tests = Nil,
	  		         taus = Nil,
	  		         sums = Nil)
	}
	
	private def createAction(subEnvironment: Environment[String, Name])(action: PreAction):
	  (Option[Action], Option[Action], Option[Action], Option[Action]) = {
	  	  
	  def returnFreeNameOutput(action: Action)  = (Some(action), None, None, None)
	  def returnBoundNameOutput(action: Action) = (None, Some(action), None, None)
	  def returnFreeNameInput(action: Action)   = (None, None, Some(action), None)
	  def returnBoundNameInput(action: Action)  = (None, None, None, Some(action))
	  
	  val (label, variable, parameters) = action
	  label match {
	    case ml.Input(channel, arguments) =>
	    	val channelName = subEnvironment.getOrElse(channel, Free(channel))
	      val parameterNames = Array.fill[Name](parameters.length)(Internal(0)).toList
	      parameters.foreach(subEnvironment.add(_, Internal(0)))
	      val argumentNames = arguments.map(arg => subEnvironment.getOrElse(arg, Free(arg)))
	      parameters.foreach(subEnvironment.remove(_))
	      channelName match {
	        case Restricted(_) => 
	          returnBoundNameInput((Input, channelName, parameterNames, variable, argumentNames))
	        case _ =>
	          returnFreeNameInput((Input, channelName, parameterNames, variable, argumentNames))
	      }
	    case ml.Output(channel, arguments) =>
	    	val channelName = subEnvironment.getOrElse(channel, Free(channel))
	      val parameterNames = parameters.map(p => subEnvironment.getOrElse(p, Free(p)))
	      val argumentNames = arguments.map(a => subEnvironment.getOrElse(a, Free(a)))
	      channelName match {
	        case Restricted(_) => 
	          returnBoundNameOutput((Output, channelName, parameterNames, variable, argumentNames))
	        case _ =>
	          returnFreeNameOutput((Output, channelName, parameterNames, variable, argumentNames))
	      }
	  }
	}
	
	private def createActions(subEnvironment: Environment[String, Name])(actions: List[PreAction]):
		(List[Action], List[Action], List[Action], List[Action]) = {
	  val transformedActions = for(action <- actions) yield createAction(subEnvironment)(action)
	  val freeNameInputs = (for(action <- transformedActions) yield action._1).flatten
	  val boundNameInputs = (for(action <- transformedActions) yield action._2).flatten
	  val freeNameOutputs = (for(action <- transformedActions) yield action._3).flatten
	  val boundNameOutputs = (for(action <- transformedActions) yield action._4).flatten
	  (freeNameInputs, boundNameInputs, freeNameOutputs, boundNameOutputs)
	}
	
	private def createTau(subEnvironment: Environment[String, Name]): PreTau => Tau = {
	  case (variable, arguments) =>
	    val argumentNames = arguments.map(a => subEnvironment.getOrElse(a, Free(a)))
	    (variable, argumentNames)
	}
	
	private def createTaus(subEnvironment: Environment[String, Name]): List[PreTau] => List[Tau] =
	  Monoid.extend(createTau(subEnvironment))
	  
	private def createTest(subEnvironment: Environment[String, Name]): PreTest => Test = {
	  case (testType, left, right, variable, arguments) =>
	    val leftName = subEnvironment.getOrElse(left, Free(left))
	    val rightName = subEnvironment.getOrElse(right, Free(right))
	    val argumentNames = arguments.map(n => subEnvironment.getOrElse(n, Free(n)))
	    (testType, leftName, rightName, variable, argumentNames)
	}

	private def createTests(subEnvironment: Environment[String, Name]): List[PreTest] => List[Test] =
	  Monoid.extend(createTest(subEnvironment))
	  
	private def createSum(subEnvironment: Environment[String, Name]): PreSum => Sum = {
	  case (acts, tests, taus) => 
	    (createSumActions(subEnvironment)(acts), createTests(subEnvironment)(tests), createTaus(subEnvironment)(taus))
	}
	
	private def createSums(subEnvironment: Environment[String, Name]): List[PreSum] => List[Sum] =
	  Monoid.extend(createSum(subEnvironment))
	
	private def createSumAction(subEnvironment: Environment[String, Name]): PreAction => Action = {
	  case (label, variable, arguments) =>
	  label match {
	    case ml.Input(channel, parameters) =>
	    	val channelName = subEnvironment.getOrElse(channel, Free(channel))
	      val parameterNames = Array.fill[Name](parameters.length)(Internal(0)).toList
	      parameters.foreach(subEnvironment.add(_, Internal(0)))
	      val argumentNames = arguments.map(arg => subEnvironment.getOrElse(arg, Free(arg)))
	      parameters.foreach(subEnvironment.remove(_))
	      (Input, channelName, parameterNames, variable, argumentNames)
	    case ml.Output(channel, parameters) =>
	    	val channelName = subEnvironment.getOrElse(channel, Free(channel))
	      val parameterNames = parameters.map(p => subEnvironment.getOrElse(p, Free(p)))
	      val argumentNames = arguments.map(arg => subEnvironment.getOrElse(arg, Free(arg)))
	      (Output, channelName, parameterNames, variable, argumentNames)
	  }
	}
	
	private def createSumActions(subEnvironment: Environment[String, Name]): List[PreAction] => List[Action] =
	  Monoid.extend(createSumAction(subEnvironment))
	
	
}
















