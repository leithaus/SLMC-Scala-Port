package biosimilarity.slmc.ast.ml

import biosimilarity.slmc.util.Showable
import scala.collection.mutable
import scala.collection.immutable.HashMap
import biosimilarity.slmc.util.OCaml._
import biosimilarity.slmc.util.Monoid
import biosimilarity.slmc.util.Environment

sealed abstract class ModalLogic extends ModalLogicLike
case object True extends ModalLogic
case object False extends ModalLogic
case object Void extends ModalLogic
case class Compare(i: Integer, t: ComparisonType) extends ModalLogic
case class Equal(id1: String, id2: String) extends ModalLogic
case class NotEqual(id1: String, id2: String) extends ModalLogic
case class Compose(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Decompose(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Not(f: ModalLogic) extends ModalLogic
case class And(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Or(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Implies(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Equivalent(f1: ModalLogic, f2: ModalLogic) extends ModalLogic
case class Reveal(s: String, f: ModalLogic) extends ModalLogic
case class RevealAll(s: String, f: ModalLogic) extends ModalLogic
case class Fresh(s: String, f: ModalLogic) extends ModalLogic
case class Free(s: String) extends ModalLogic
case class Hidden(s: String, f: ModalLogic) extends ModalLogic
case class MayTau(f: ModalLogic) extends ModalLogic
case class AllTau(f: ModalLogic) extends ModalLogic
case class MayLabelled(l: Label, f: ModalLogic) extends ModalLogic
case class AllLabelled(l: Label, f: ModalLogic) extends ModalLogic
case class MayOutputN(s: String, f: ModalLogic) extends ModalLogic
case class MayInputN(s: String, f: ModalLogic) extends ModalLogic
case class AllOutputN(s: String, f: ModalLogic) extends ModalLogic
case class AllInputN(s: String, f: ModalLogic) extends ModalLogic
case class MayOutput(f: ModalLogic) extends ModalLogic
case class MayInput(f: ModalLogic) extends ModalLogic
case class AllOutput(f: ModalLogic) extends ModalLogic
case class AllInput(f: ModalLogic) extends ModalLogic
case class MayN(s: String, f: ModalLogic) extends ModalLogic
case class AllN(s: String, f: ModalLogic) extends ModalLogic
case class May(f: ModalLogic) extends ModalLogic
case class All(f: ModalLogic) extends ModalLogic
case class Exists(s: String, f: ModalLogic) extends ModalLogic
case class ForAll(s: String, f: ModalLogic) extends ModalLogic
case class MaximumFixpoint(variable: String, parameters: List[String], formula: ModalLogic, arguments: List[String]) extends ModalLogic
case class MinimumFixpoint(variable: String, parameters: List[String], formula: ModalLogic, arguments: List[String]) extends ModalLogic
case class Eventually(f: ModalLogic) extends ModalLogic
case class Always(f: ModalLogic) extends ModalLogic
case class Inside(f: ModalLogic) extends ModalLogic
case class ShowFails(f: ModalLogic) extends ModalLogic
case class ShowSucceeds(f: ModalLogic) extends ModalLogic
case class PropositionVariable(s: String, sl: List[String]) extends ModalLogic
case class Abbreviate(s: String, fs: List[ModalLogic]) extends ModalLogic
		
sealed abstract class Label
case class Output(channel: String, arguments: List[String]) extends Label
case class Input(channel: String, arguments: List[String]) extends Label

sealed abstract class ComparisonType
case object EqNum extends ComparisonType
case object GtNum extends ComparisonType
case object LtNum extends ComparisonType
  
trait ModalLogicLike extends Showable {
  
  def show(): String = {
    this match {
      case True =>
        "true"
      case False =>
        "false"
      case Void =>
        "void"
      case Compare(i,EqNum) =>
        i.toString
      case Compare(i,LtNum) =>
        "< %d".format(i)
      case Compare(i,GtNum) =>
        "> %d".format(i)
      case Equal(id1,id2) => 
        "%s == %s".format(id1, id2)
      case NotEqual(id1,id2) => 
        "%s != %s".format(id1, id2)
      case Compose(f1,f2) =>
        "(%s | %s)".format(f1.show, f2.show)
      case Decompose(f1,f2) =>
        "(%s || %s)".format(f1.show, f2.show)
      case Not(f) =>
        "not (%s)".format(f.show)
      case And(f1,f2) =>
        "(%s and %s)".format(f1.show, f2.show)
      case Or(f1,f2) =>
        "(%s or %s)".format(f1.show, f2.show)
      case Implies(f1,f2) =>
        "(%s => %s)".format(f1.show, f2.show)
      case Equivalent(f1,f2) =>
        "(%s <=> %s)".format(f1.show, f2.show)
      case Reveal(s,f1) =>
        "reveal %s.(%s)".format(s, f1.show)
      case RevealAll(s,f) =>
        "revealall %s.(%s)".format(s, f.show)
      case Fresh(s,f) =>
        "fresh %s.(%s)".format(s, f.show)
      case Free(s) =>
        "@%s".format(s)
      case Hidden(s,f) =>
        "hidden %s.(%s)".format(s, f.show)
      case MayTau(f) =>
        "<> (%s)".format(f.show)
      case AllTau(f) =>
        "[] (%s)".format(f.show)
      case MayLabelled(l,f) =>
        "<%s> (%s)".format(l, f.show)
      case AllLabelled(l,f) =>
        "[%s] (%s)".format(l, f.show)
      case MayOutputN(n,f) =>
        "<%s!> (%s)".format(n, f.show)
      case MayInputN(n,f) =>
        "<%s?> (%s)".format(n, f.show)
      case AllOutputN(n,f) =>
        "[%s!] (%s)".format(n, f.show)
      case AllInputN(n,f) =>
        "[%s?] (%s)".format(n, f.show)
      case MayOutput(f) =>
        "<!> (%s)".format(f.show)
      case MayInput(f) =>
        "<?> (%s)".format(f.show)
      case AllOutput(f) =>
        "[!] (%s)".format(f.show)
      case AllInput(f) =>
        "[?] (%s)".format(f.show)
      case MayN(n,f) =>
        "<%s> (%s)".format(n, f.show)
      case AllN(n,f) =>
        "[%s] (%s)".format(n, f.show)
      case May(f) =>
        "<*> (%s)".format(f.show)
      case All(f) =>
        "[*] (%s)".format(f.show)
      case Exists(s,f) =>
        "exists %s.(%s)".format(s, f.show)
      case ForAll(s,f) =>
        "forall %s.(%s)".format(s, f.show)
      case MaximumFixpoint(x, VarArg(parameters), f, VarArg(arguments)) =>
        "(maxfix %s%s.(%s))%s".format(x, parameters, f.show, arguments)
      case MinimumFixpoint(x, VarArg(parameters), f, VarArg(arguments)) =>
        "(minfix %s%s.(%s))%s".format(x, parameters, f.show, arguments)
      case Eventually(f) =>
        "eventually (%s)".format(f.show)
      case Always(f) =>
        "always (%s)".format(f.show)
      case Inside(f) =>
        "inside (%s)".format(f.show)
      case ShowFails(f) =>
        "show_fail (%s)".format(f.show)
      case ShowSucceeds(f) =>
        "show_succeed (%s)".format(f.show)
      case PropositionVariable(p, VarArg(parameters)) =>
        "%s%s".format(p, parameters)
      case Abbreviate(id, forms) =>
        val formulas =
	        forms match {
	        	case Nil => 
	        		""
	        	case hd::tl =>
	        	  "(%s%s)".format(hd.show, intercalate("")(tl.map(_.show)))
	        }
        "%s%s".format(id, formulas)
    }
  }
  
  /** Returns the formula ast, the free names and the free propositional variables regarding a name substitution */
  def substitute(refresh: Environment[String, String]): (ModalLogic, List[String], List[String]) = {
  	var res: List[String] = Nil
  	var variables: List[String] = Nil
  	val aux = new Environment[String, Boolean]()
  	val environment = new Environment[String, Boolean]()
  	
  	def substituteName: String => String = {
  	  case "_" => "_"
  	  case id =>
  	    val newId = refresh.getOrElse(id, id)
  	    if(!aux.mem(newId)) {
  	      aux.add(newId, true)
  	      res = newId::res
  	    }
  	    newId
  	}
  	
  	def substituteNames = Monoid.extend(substituteName)
  	
    def substitute: ModalLogicLike => ModalLogic = {
      case True => True
      case False => False
      case Void => Void
      case Compare(i, t) => Compare(i,t)
      case Equal(id1, id2) => 
      val nid1 = refresh.getOrElse(id1, id1)
      val nid2 = refresh.getOrElse(id2, id2)
      if(!aux.mem(nid1)) {
        aux.add(nid1, true)
        res = nid1::res
      }
      if(!aux.mem(nid2)) {
        aux.add(nid2, true)
        res = nid2::res
      }
      Equal(nid1, nid2)
      case NotEqual(id1, id2) =>
      val nid1 = refresh.getOrElse(id1, id1)
      val nid2 = refresh.getOrElse(id2, id2)
      if(!aux.mem(nid1)) {
        aux.add(nid1, true)
        res = nid1::res
      }
      if(!aux.mem(nid2)) {
        aux.add(nid2, true)
        res = nid2::res
      }
      NotEqual(nid1, nid2)
      case Compose(f1, f2) => 
        Compose(substitute(f1), substitute(f2))
      case Decompose(f1, f2) => 
        Decompose(substitute(f1), substitute(f2))
      case Not(f) => 
        Not(substitute(f))
      case And(f1, f2) => 
        And(substitute(f1), substitute(f2))
      case Or(f1, f2) => 
        Or(substitute(f1), substitute(f2))
      case Implies(f1, f2) =>
        Implies(substitute(f1), substitute(f2))
      case Equivalent(f1, f2) =>
        Equivalent(substitute(f1), substitute(f2))
      case Reveal(s, f) =>
	      val ns = refresh.getOrElse(s, s)
	      if(!aux.mem(ns)) {
	        aux.add(ns, true)
	        res = ns::res
	      }
	      Reveal(ns, substitute(f))
      case RevealAll(s,f) =>
	      val ns = refresh.getOrElse(s, s)
	      if(!aux.mem(ns)) {
	        aux.add(ns, true)
	        res = ns::res
	      }
	      RevealAll(ns, substitute(f))
      case Fresh(s,f) =>
	      refresh.add(s, s);
	      aux.add(s, false)
	      val res = substitute(f)
	      refresh.remove(s)
	      aux.remove(s)
	      Fresh(s,res)
      case Free(s) =>
	      val ns = refresh.getOrElse(s, s)
	      if(!aux.mem(ns)) {
	        aux.add(ns, true)
	        res = ns::res
	      }
	      Free(ns)
      case Hidden(s,f) =>
	      refresh.add(s, s)
	      aux.add(s, false)
	      val res = substitute(f)
	      refresh.remove(s)
	      aux.remove(s)
	      Hidden(s,res)
      case MayTau(f) => MayTau(substitute(f))
      case AllTau(f) => AllTau(substitute(f))
      case MayLabelled(Input(channel, arguments),f) =>
        MayLabelled(Input(substituteName(channel), substituteNames(arguments)), substitute(f))
      case MayLabelled(Output(channel, arguments),f) =>
        MayLabelled(Output(substituteName(channel), substituteNames(arguments)), substitute(f))
      case AllLabelled(Input(channel, arguments),f) =>
        AllLabelled(Input(substituteName(channel), substituteNames(arguments)), substitute(f))
      case AllLabelled(Output(channel, arguments),f) =>
        AllLabelled(Output(substituteName(channel), substituteNames(arguments)), substitute(f))
      case MayOutputN(name, f) =>
        val newName = refresh.getOrElse(name, name)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      MayOutputN(newName, substitute(f))
      case MayInputN(name, f) =>
	      val newName = refresh.getOrElse(name, name)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      MayInputN(newName, substitute(f))
      case AllOutputN(n, f) =>
	      val newName = refresh.getOrElse(n, n)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      AllOutputN(newName, substitute(f))
      case AllInputN(n,f) =>
	      val newName = refresh.getOrElse(n, n)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      AllInputN(newName, substitute(f))
      case MayOutput(f) => 
        MayOutput(substitute(f))
      case MayInput(f) => 
        MayInput(substitute(f))
      case AllOutput(f) =>
        AllOutput(substitute(f))
      case AllInput(f) =>
        AllInput(substitute(f))
      case MayN(n, f) =>
	      val newName = refresh.getOrElse(n, n)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      MayN(newName, substitute(f))
      case AllN(n, f) =>
	      val newName = refresh.getOrElse(n, n)
        if(!aux.mem(newName)) {
          aux.add(newName, true)
          res = newName::res
        }
	      AllN(newName, substitute(f))
      case May(f) =>
        May(substitute(f))
      case All(f) =>
        All(substitute(f))
      case Exists(s, f) =>
        refresh.add(s, s)
        aux.add(s, false)
        val res = substitute(f)
        refresh.remove(s)
        aux.remove(s)
      Exists(s,res)
      case ForAll(s, f) =>
	      refresh.add(s, s)
	      aux.add(s, false)
        val res = substitute(f)
        refresh.remove(s)
        aux.remove(s)
        ForAll(s,res)
      case MaximumFixpoint(x, params, f, args) =>
	      environment.add(x, false)
	      params.foreach (n => aux.add(n, false))
	      params.foreach (n => refresh.add(n, n))
	      val result = substitute(f)
	      environment.remove(x)
	      params.foreach (aux.remove(_))
	      params.foreach (refresh.remove(_))
	      MaximumFixpoint(x, params, result, substituteNames(args))
      case MinimumFixpoint(x, params, f, args) => 
	      environment.add(x, false)
	      params.foreach (n => aux.add(n, false))
	      params.foreach (n => refresh.add(n, n))
	      val result = substitute(f)
	      environment.remove(x)
	      params.foreach (aux.remove(_))
	      params.foreach (refresh.remove(_))
	      MinimumFixpoint(x, params, result, substituteNames(args))
      case Eventually(f) =>
        Eventually(substitute(f))
      case Always(f) =>
        Always(substitute(f))
      case Inside(f) =>
        Inside(substitute(f))
      case ShowFails(f) =>
        ShowFails(substitute(f))
      case ShowSucceeds(f) =>
        ShowSucceeds(substitute(f))
      case PropositionVariable(p, args) => 
      if(!environment.mem(p)) {
      	environment.add(p, true)
      	variables = p::variables
      }
      PropositionVariable(p, substituteNames(args))
      case Abbreviate(id, fs) =>
        Abbreviate(id,fs)
    }
    (substitute(this), res, variables)
  }
  
  def showSubst(nenv: Environment[String, String]): String = {
    val (ml, _, _) = this.substitute(nenv)
    ml.show
  }
  
  def freeNames(nameEnvironment: Environment[String, String]): (List[String], List[String]) = {
    var res: List[String] = Nil
    var variables: List[String] = Nil
    val aux = new Environment[String, Boolean]
    val environment = new Environment[String, Boolean]
    
    def declare(id: String) {
      val nid = nameEnvironment.getOrElse(id, id)
      if(aux.mem(nid)) {
        aux.add(nid, true)
        res = nid::res
      }
    }

    def freeNames: ModalLogicLike => Unit = {
      case True => ;
      case False => ;
      case Void => ;
      case Compare(_, _) => ;
      case Equal(id1, id2) =>
        declare(id1)
        declare(id2)
      case NotEqual(id1, id2) =>
        declare(id1)
        declare(id2)
      case Compose(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Decompose(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Not(f) =>
        freeNames(f)
      case And(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Or(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Implies(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Equivalent(f1, f2) =>
        freeNames(f1)
        freeNames(f2)
      case Reveal(s, f) =>
        declare(s)
        freeNames(f)
      case RevealAll(s, f) =>
        declare(s)
        freeNames(f)
      case Fresh(s, f) =>
        nameEnvironment.add(s, s)
        aux.add(s, false)
        freeNames(f)
        nameEnvironment.remove(s)
        aux.remove(s)
      case Free(s) =>
        declare(s)
      case Hidden(s, f) =>
        nameEnvironment.add(s, s)
        aux.add(s, false)
        freeNames(f)
        nameEnvironment.remove(s)
        aux.remove(s)
      case MayTau(f) =>
        freeNames(f)
      case AllTau(f) =>
        freeNames(f)
      case MayLabelled(Input(channel, arguments), f) =>
        for(id <- channel::arguments)
          declare(id)
      case MayLabelled(Output(channel, arguments), f) =>
        for(id <- channel::arguments)
          declare(id)
      case AllLabelled(Input(channel, arguments), f) =>
        for(id <- channel::arguments)
          declare(id)
      case AllLabelled(Output(channel, arguments), f) =>
        for(id <- channel::arguments)
          declare(id)
      case MayOutputN(s, f) =>
        declare(s)
        freeNames(f)
      case MayInputN(s, f) =>
        declare(s)
        freeNames(f)
      case AllOutputN(s, f) =>
        declare(s)
        freeNames(f)
      case AllInputN(s, f) =>
        declare(s)
        freeNames(f)
      case MayOutput(f) =>
        freeNames(f)
      case MayInput(f) =>
        freeNames(f)
      case AllOutput(f) =>
        freeNames(f)
      case AllInput(f) =>
        freeNames(f)
      case MayN(s, f) =>
        declare(s)
        freeNames(f)
      case AllN(s, f) =>
        declare(s)
        freeNames(f)
      case May(f) =>
        freeNames(f)
      case All(f) =>
        freeNames(f)
      case Exists(s, f) =>
        nameEnvironment.add(s, s)
        aux.add(s, false)
        freeNames(f)
        nameEnvironment.remove(s)
        aux.remove(s)
      case ForAll(s, f) =>
        nameEnvironment.add(s, s)
        aux.add(s, false)
        freeNames(f)
        nameEnvironment.remove(s)
        aux.remove(s)
      case MaximumFixpoint(x, paramList, f, argList) =>
        environment.add(x, false)
        for(n <- paramList) { nameEnvironment.add(n, n) }
        for(n <- paramList) { aux.add(n, false) }
        freeNames(f)
        for(n <- paramList) { nameEnvironment.remove(n) }
        for(n <- paramList) { aux.remove(n) }
        for(n <- argList) { declare(n) }
        environment.remove(x)
      case MinimumFixpoint(x, paramList, f, argList) =>
        environment.add(x, false)
        for(n <- paramList) { nameEnvironment.add(n, n) }
        for(n <- paramList) { aux.add(n, false) }
        freeNames(f)
        for(n <- paramList) { nameEnvironment.remove(n) }
        for(n <- paramList) { aux.remove(n) }
        for(n <- argList) { declare(n) }
        environment.remove(x)
      case Eventually(f) =>
        freeNames(f)
      case Always(f) =>
        freeNames(f)
      case Inside(f) =>
        freeNames(f)
      case ShowFails(f) =>
        freeNames(f)
      case ShowSucceeds(f) =>
        freeNames(f)
      case PropositionVariable(s, sl) =>
        if(!environment.mem(s)) {
          environment.add(s, true)
          for(n <- sl) {
            declare(n)
          }
        }
      case Abbreviate(_, _) => ;
    }
    freeNames(this)
    (res, variables)
  }
  
}

















