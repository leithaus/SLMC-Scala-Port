package biosimilarity.slmc.ast.pc

import scala.collection.immutable.HashMap
import biosimilarity.slmc.util.Namegen._
import biosimilarity.slmc.util.Showable
import biosimilarity.slmc.ast.cc
import biosimilarity.slmc.ast.cc._
import biosimilarity.slmc.ast.sr.UndeclaredIdentifier
import biosimilarity.slmc.ast.sr.IllFormedAst
import biosimilarity.slmc.ast.sr.UnguardedRecursion

sealed abstract class PiCalculus extends PiCalculusLike
case object Void extends PiCalculus
case class Parallel(left: PiCalculus, right: PiCalculus) extends PiCalculus
case class Sum(left: PiCalculus, right: PiCalculus) extends PiCalculus
case class New(names: List[String], process: PiCalculus) extends PiCalculus
case class Action(action: ActionType, next: PiCalculus) extends PiCalculus
case class Test(left: String, right: String, process: PiCalculus, test: TestType) extends PiCalculus
case class Variable(name: String, arguments: List[String]) extends PiCalculus

sealed abstract class TestType
case object Equals extends TestType
case object Differs extends TestType

sealed abstract class ActionType
case class Input(channel: String, arguments: List[String]) extends ActionType
case class Output(channel: String, arguments: List[String]) extends ActionType
case object Tau extends ActionType

trait PiCalculusLike extends Showable {
  
  type GlobalEnvironment = Map[String, (List[String], PiCalculus)]
	
	def show(): String = {
    this match {
    case Void =>
      "0"
    case Parallel(left, right) =>
      "(%s | $s)".format(left.show, right.show)
    case Sum(ast1, ast2) =>
      "{%s + %s}".format(ast1.show, ast2.show)
    case New(ids, ast) =>
      "new %s in %s".format(intercalate(",")(ids), ast.show)
    case Action(a, ast) =>
      a match {
        case Input(n, ids) =>
          "%s?(%s).%s".format(n, intercalate(",")(ids), ast.show)
        case Output(n, ids) =>
          "%s!(%s).%s".format(n, intercalate(",")(ids), ast.show)
        case Tau =>
          "tau."
      }
    case Test(id1, id2, ast, typ) =>
      val equality = if(typ == Equals) { "=" } else { "!=" }
      "[%s %s %s].%s".format(id1, equality, id2, ast.show)
    case Variable(name, arguments) =>
      if(arguments.length > 0) {
        "%s(%s)".format(name, intercalate(",")(arguments))
      } else {
        name
      }
    }
  }
	
	
	def substitute(refresh: Map[String, String]): PiCalculus = 
	  this match {
		case Void => 
		  Void
		case Parallel(left, right) =>
		  Parallel(left.substitute(refresh), right.substitute(refresh))
		case Sum(left, right) =>
		  Sum(left.substitute(refresh), right.substitute(refresh))
		case New(names, process) =>
		  val mapping = names.map((_, generateBoundName))
		  val newProcess = process.substitute(refresh ++ mapping)
		  New(mapping.unzip._2, newProcess)
		case Action(Input(channel, arguments), process) =>
		  val newChannel = refresh.getOrElse(channel, channel)
		  val mapping = arguments.map((_, generateBoundName))
		  val newProcess = process.substitute(refresh ++ mapping)
		  Action(Input(newChannel, mapping.unzip._2), newProcess)
		case Action(Output(channel, arguments), process) =>
		  val newChannel = refresh.getOrElse(channel, channel)
		  val newArguments = arguments.map(argument => refresh.getOrElse(argument, argument))
		  val newProcess = process.substitute(refresh)
		  Action(Output(newChannel, newArguments), newProcess)
		case Action(Tau, process) =>
		  Action(Tau, process.substitute(refresh))
		case Test(left, right, process, test) =>
		  val newLeft = refresh.getOrElse(left, left)
		  val newRight = refresh.getOrElse(right, right)
		  val newProcess = process.substitute(refresh)
		  Test(newLeft, newRight, newProcess, test)
		case Variable(name: String, arguments: List[String]) =>
		  Variable(name, arguments.map(n => refresh.getOrElse(n, n)))
	}
	
	def freeVariables(): Set[String] = 
		this match{
		  case Void => 
		    Set()
	    case Parallel(left, right) => 
	      left.freeVariables ++ right.freeVariables
	    case Sum(left, right) =>
	      left.freeVariables() ++ right.freeVariables
	    case New(names, process) =>
	      process.freeVariables -- Set(names: _*)
	    case Action(Input(channel, arguments), process) =>
	      Set(channel) ++ (process.freeVariables -- Set(arguments: _*))
	    case Action(Output(channel, arguments), process) =>
	      Set(channel) ++ process.freeVariables
	    case Action(Tau, process) =>
	      process.freeVariables
	    case Test(_, _, process, _) =>
	      process.freeVariables
	    case Variable(id, arguments) =>
	      Set(id::arguments: _*)
		}
	
	def isVoid(globals: GlobalEnvironment): Boolean =
	  this match {
	  case Void => 
	    true
	  case Parallel(left, right) => 
	    left.isVoid(globals) && right.isVoid(globals)
	  case Sum(left, right) =>
	    left.isVoid(globals) && right.isVoid(globals)
	  case New(_, process) =>
	    process.isVoid(globals)
	  case Variable(name, _) =>
	    globals.get(name) match {
	      case Some((_,process)) => process.isVoid(globals)
	      case _ => throw UndeclaredIdentifier(name)
	    }
  }
	
	def checkForUnguardedRecursion(env: Map[String, (List[String], PiCalculus)], pId: String, visited: List[String]) {
	  this match {
      case Parallel(p1, p2) =>
        p1.checkForUnguardedRecursion(env, pId, visited)
        p2.checkForUnguardedRecursion(env, pId, visited)
      case New(nl, p) =>
        p.checkForUnguardedRecursion(env, pId, visited)
      case Variable(id, al) =>
        if (id.equals(pId)) {
          throw UnguardedRecursion(pId)
        } else {
          if (!visited.contains(id)) {
          	env.get(id) match {
          	  case Some((_, p)) =>
          	    p.checkForUnguardedRecursion(env, pId, id::visited)
          	  case None =>
          	    throw UndeclaredIdentifier(id)
          	}
          }
        }
      case _ => ;
	  }
}
	
	
}

object PiCalculus {
  
  /** Converts a ConversationCalculus to a PiCalculus */
  def apply(upConversation: String, hereConversation: String, recAux: PiCalculus): ConversationCalculus => PiCalculus = {
    def apply: ConversationCalculus => PiCalculus = {
	    case Inaction => 
	      Void
	    case cc.Parallel(ast1, ast2) =>
	      Parallel(apply(ast1), apply(ast2))
	    case cc.Sum(astl) =>
	      val label = freshAlias
	      val f = freshAlias
	      val (process, direction, arguments) = translateList(upConversation, hereConversation, label, f, recAux)(astl)
	      val conversation =
	        direction match {
	          case Here => hereConversation
	          case Up => upConversation
	        }
	      Action(Input(conversation, label::(f::arguments)), process)
	    case Context(conversation, process) =>
	      PiCalculus(hereConversation, conversation, recAux)(process)
	    case This(thisVariable, process) =>
	      val nonce = freshAlias()
        New(List(nonce),
          Action(Tau,
            Action(Tau,
              Parallel(Action(Output(nonce, List(hereConversation)), Void),
                Action(Input(nonce,List(thisVariable)), apply(process))))))
      case cc.Action(actionType, process) =>
        translateActionType(process, upConversation, hereConversation, recAux)(actionType)
      case Definition(label, process) =>
        val (labelX, f, conversation) = (freshAlias(), freshAlias(), freshAlias())
        Action(Input(hereConversation, labelX::f::List(conversation)),
          Test(labelX, label,
            Parallel(Action(Input(f,Nil),
              Parallel(PiCalculus(hereConversation, conversation, recAux)(process), recAux)),
              Action(Output(f,Nil), Void)), Equals))
      case cc.New(conversation, label, process) =>
        val (f, fConv) = (freshAlias(), freshAlias())
        New(f::List(fConv), Action(Output(conversation, label::f::List(fConv)), PiCalculus(hereConversation, fConv, recAux)(process)))
      case Join(conv, label, ast) =>
        val f = freshAlias()
        New(List(f), Action(Output(conv, label::f::List(hereConversation)), apply(ast)))
      case cc.Variable(rVar, ids) =>
        Variable(rVar, upConversation::hereConversation::ids)
      case IfThenElse(astt, aste) =>
        val nonce = freshAlias()
        New(List(nonce),
          Action(Tau, Sum(Action(Tau, Parallel(Action(Output(nonce, Nil), Void),
            Action(Input(nonce, Nil),
              apply(astt)))),
            Action(Tau, Parallel(Action(Output(nonce, Nil), Void),
              Action(Input(nonce, Nil),
                apply(aste)))))))
	      
    }
  apply
  }
  
  private def translateList(upConversation: String, hereConversation: String, labelX: String, f: String, recAux: PiCalculus):
  	List[ConversationCalculus] => (PiCalculus, Direction, List[String]) = {
    case Nil => (Void, Here, Nil)
    case hd::Nil =>
      hd match {
        case cc.Action(cc.Input(dir, label, args), process) =>
          (Test(labelX, label, Parallel(
            Action(Input(f, Nil), PiCalculus(upConversation, hereConversation, recAux)(process)),
            Action(Output(f, Nil), Void)), Equals),
            dir, args)
        case _ => throw IllFormedAst
      }
    case hd::tl =>
      val (left, dir1, args1) = translateList(upConversation, hereConversation, labelX, f, recAux)(tl)
      hd match {
        case cc.Action(cc.Input(dir, label, args), process) =>
          if(dir == dir1 && testIds(args, args1)) {
            (Sum (left,
              Test(labelX, label,
                Parallel(Action(Input(f, Nil), PiCalculus(upConversation, hereConversation, recAux)(process)),
                  Action(Output(f, Nil), Void)), Equals)), dir, args)
          } else {
            throw IllFormedAst
          }
        case _ => throw IllFormedAst
      }
  }
  	
  private def translateActionType(process: ConversationCalculus, upConversation: String, hereConversation: String, recAux: PiCalculus):
    cc.ActionType => PiCalculus = {
    case cc.Input(dir, label, args) =>
      val (labelX, f) = (freshAlias(), freshAlias())
      val conv = if(dir == Here) hereConversation else upConversation
      Action(Input(conv, labelX::f::args),
        Test(labelX, label,
          Parallel(Action(Input(f, Nil), PiCalculus(upConversation, hereConversation, recAux)(process)),
              Action(Output(f, Nil), Void)), Equals))
    case cc.Output(dir, label, args) =>
      val f = freshAlias()
      val conv = if(dir == Here) hereConversation else upConversation
      New(List(f), Action(Output(conv, label::f::args), PiCalculus(upConversation, hereConversation, recAux)(process)))
  }
  	
  private def testIds(ids1: List[String], ids2: List[String]): Boolean = {
    (ids1, ids2) match {
      case (Nil, Nil) => true
      case (hd1::tl1, hd2::tl2) => (hd1.equals(hd2)) && testIds(tl1, tl2)
      case _ => false
    }
  }
  	
  	
}

















