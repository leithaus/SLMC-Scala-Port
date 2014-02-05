package biosimilarity.slmc

import scala.concurrent._
import ExecutionContext.Implicits.global
import biosimilarity.slmc.util.Logger
import biosimilarity.slmc.ast.ml.ModalLogic
import biosimilarity.slmc.ast.sr.UndeclaredIdentifier
import biosimilarity.slmc.ast.sr.WrongArgumentCount
import data.Process
import data.Equation
import biosimilarity.slmc.util.Environment
import biosimilarity.slmc.ast.sr.IllFormedAst
import biosimilarity.slmc.util.Namegen
import biosimilarity.slmc.data.iterator._
import biosimilarity.slmc.util.Monoid
import biosimilarity.slmc.util.OCaml.NotFound
import biosimilarity.slmc.data.Process.ProcessElt
import biosimilarity.slmc.util.OCaml.Ref
import scala.concurrent.duration._
import scala.actors.threadpool.TimeoutException
import biosimilarity.slmc.ast.sr.CheckerTimedOut

case class Checker() {
  
  var maxThreads: Int = 5000
  var showCheckCounter: Boolean = false
  var showTime: Boolean = false
  var showTrace: Boolean = false
  var checkCounter: Int = 0
  var timeout: Duration = Duration(5000, MILLISECONDS)
  
  sealed abstract class Fixpoints
  case object Max extends Fixpoints
  case object Min extends Fixpoints
  
  def check(env: SLMC, processId: String, arguments: List[String], prop: ModalLogic): (Boolean, String) = {
    if(!env.allClosures.contains(processId)) 
      throw UndeclaredIdentifier(processId)
    
		val logger = new Logger()
    
    def check(process: Process, prop: ModalLogic): Boolean = {
      var nenv = new Environment[String, String]() // This is var because it gets masked during MinFixpoint and MaxFixpoint
      val penv = new Environment[String, (List[(Set[ProcessElt], List[String])], ModalLogic, List[String], List[String], Fixpoints, Int)]
      import ast.ml._
      
      
      def check(process: Process): ModalLogic => Boolean = {
        case True => true
		    case False => false
		    case Void => process.isEmpty()
		    case Compare(i, EqNum) =>
		      if (i == 1) {
		        !process.isEmpty() && process.countComponents() == 1
		      } else {
		        process.countComponents() == i
		      }
		    case Compare(i, LtNum) =>
		      if(i == 0) {
		         false
		      } else if(i == 1) {
		        process.isEmpty()
		      } else {
		        process.countComponents() < i
		      }
		    case Compare(i, GtNum) =>
		      !process.isEmpty() && process.countComponents() > i
		    case Equal(id1, id2) =>
		      val nid1 = nenv.getOrElse(id1, id1)
		      val nid2 = nenv.getOrElse(id2, id2)
		      nid1 == nid2
		    case NotEqual(id1, id2) =>
		      val nid1 = nenv.getOrElse(id1, id1)
		      val nid2 = nenv.getOrElse(id2, id2)
		      nid1 != nid2
		    case Not(f) => 
		      !check(process)(f)
		    case And(f1, f2) =>
		      check(process)(f1) && check(process)(f2)
		    case Or(f1, f2) =>
		      check(process)(f1) || check(process)(f2)
		    case Implies(f1, f2) =>
		      !check(process)(f1) || check(process)(f2)
		    case Equivalent(f1, f2) =>
		      ((!check(process)(f1) || check(process)(f2))
		        && (!check(process)(f2) || check(process)(f1)))
		    case Decompose(f1, f2) =>
		      new CompositionIterator(process).exists({
		        case (processA, processB) => !check(processA)(f1) && !check(processB)(f2)
		      })
		    case Compose(f1, f2) => 
		      new CompositionIterator(process).exists({
		        case (processA, processB) => check(processA)(f1) && check(processB)(f2)
		      })
		    case Reveal(s, f) =>
		      new RevealIterator(process, nenv.getOrElse(s, s)).exists(check(_)(f))
		    case RevealAll(s, f) =>
		      new RevealIterator(process, nenv.getOrElse(s, s)).forall(check(_)(f))
		    case Fresh(s, f) =>
		      val fresh = Namegen.freshAlias()
		      nenv.add(s, fresh)
		      val res = check(process)(f)
		      nenv.remove(s)
		      res
		    case Free(s) =>
		      val n = nenv.getOrElse(s, s)
		      process.testFreeName(n)
		    case Hidden(s, f) =>
		      val fresh = Namegen.freshAlias()
		      nenv.add(s, fresh)
		      val res = new RevealIterator(process, fresh).exists(check(_)(f))
		      nenv.remove(s)
		      logger.log("Hidden: " + res)
		      res
		    case MayTau(f) =>
		      new ReactIterator(process, RTau()).exists(check(_)(f))
		    case AllTau(f) =>
		      new ReactIterator(process, RTau()).forall(check(_)(f))
		    case MayLabelled(Input(channel, arguments), f) =>
		      val newChannel = nenv.getOrElse(channel, channel)
		      nenv.add("_","_")
		      val newArguments = arguments.map(arg => nenv.getOrElse(arg, arg))
		      nenv.remove("_")
		      new ReactIterator(process, RLab(Input(newChannel, newArguments))).exists(check(_)(f))
		    case MayLabelled(Output(channel, arguments), f) =>
		      val newChannel = nenv.getOrElse(channel, channel)
		      nenv.add("_","_")
		      val newArguments = arguments.map(arg => nenv.getOrElse(arg, arg))
		      nenv.remove("_")
		      new ReactIterator(process, RLab(Output(newChannel, newArguments))).exists(check(_)(f))
		    case AllLabelled(Input(channel, arguments), f) =>
		      val newChannel = nenv.getOrElse(channel, channel)
		      nenv.add("_","_")
		      val newArguments = arguments.map(arg => nenv.getOrElse(arg, arg))
		      nenv.remove("_")
		      new ReactIterator(process, RLab(Input(newChannel, newArguments))).forall(check(_)(f))
		    case AllLabelled(Output(channel, arguments), f) =>
		      val newChannel = nenv.getOrElse(channel, channel)
		      nenv.add("_","_")
		      val newArguments = arguments.map(arg => nenv.getOrElse(arg, arg))
		      nenv.remove("_")
		      new ReactIterator(process, RLab(Output(newChannel, newArguments))).forall(check(_)(f))
		    case MayOutputN(n, f) =>
		      val nn = nenv.getOrElse(n, n)
		      new ReactIterator(process, RName((nn, Equation.Output))).exists(check(_)(f))
		    case AllOutputN(n, f) =>
		      val nn = nenv.getOrElse(n, n)
		      new ReactIterator(process, RName((nn, Equation.Output))).forall(check(_)(f))
		    case MayOutput(f) =>
		      new ReactIterator(process, RAction(Equation.Output)).exists(check(_)(f))
		    case AllOutput(f) =>
		      new ReactIterator(process, RAction(Equation.Output)).forall(check(_)(f))
		    case MayInputN(channel, f) =>
		      val domain = createDomains(process, f, penv, nenv)._1
		      val newChannel = nenv.getOrElse(channel, channel)
		      val lengths = process.getNumArgs(newChannel)
          var res = false
	        for(length <- lengths if !res)
	          for(subList <- Monoid.orderedSublists(length, domain) if !res) {
	            res |= new ReactIterator(process, RLab(Input(newChannel, subList))).exists(check(_)(f))
	          }
	        res
		    case AllInputN(channel, f) =>
		      val domain = createDomains(process, f, penv, nenv)._1
		      val newChannel = nenv.getOrElse(channel, channel)
		      val lengths = process.getNumArgs(newChannel)
          var res = true
	        for(length <- lengths if res)
	          for(subList <- Monoid.orderedSublists(length, domain) if res) {
	            res &= new ReactIterator(process, RLab(Input(newChannel, subList))).exists(check(_)(f))
	          }
	        res
		    case MayInput(f) =>
		      val domainSub = process.freeNames()
		      var res = false
		      for(sub <- process.freeNames) {
		        res |= check(process)(MayInputN(sub, f))
		      }
		      res
		    case AllInput(f) =>
		      val domainSub = process.freeNames()
		      var res = true
		      for(sub <- process.freeNames) {
		        res &= check(process)(MayInputN(sub, f))
		      }
		      res
		    case MayN(n, f) =>
		      check(process)(MayOutputN(n, f)) || check(process)(MayInputN(n, f))
		    case AllN(n, f) =>
		      check(process)(AllOutputN(n, f)) && check(process)(AllInputN(n, f))
		    case May(f) =>
		      check(process)(MayTau(f)) || check(process)(MayOutput(f)) || check(process)(MayInput(f))
		    case All(f) =>
		      check(process)((AllTau(f))) && check(process)(AllOutput(f)) && check(process)(AllInput(f))
		    case Exists(n, f) =>
		      val domain = createDomains(process, f, penv, nenv)._1
		      var res = false
		      for(name <- domain if !res) {
		        nenv.add(n, name)
		        res |= check(process)(f)
		        nenv.remove(n)
		      }
		      res
		    case ForAll(n, f) =>
		      val domain = createDomains(process, f, penv, nenv)._1
		      var res = true
		      for(name <- domain if res) {
		        nenv.add(n, name)
		        res &= check(process)(f)
		        nenv.remove(n)
		      }
		      res
		    case MaximumFixpoint(x, params, f, args) =>
		      val (sf, nfFnsAux, pvars) = MinimumFixpoint(x, params, f, args).substitute(nenv)
		      sf match {
		        case MinimumFixpoint(nx, nparams, nf, nargs) =>
		          val nfFns = domainForm(nfFnsAux, pvars, penv)
		          val (template, marked) = argTemplate(nargs, nfFns, new Environment[String, String]())
		          val pset = Set[ProcessElt](new ProcessElt(process, marked))
		          penv.add(nx, (List((pset, template)), nf, nparams, nfFns, Max, 0))

		          // Mask nenv
		          val backupNenv = nenv
		          nenv = new Environment[String, String]()
		          for((param, arg) <- nparams.zip(nargs))
		            nenv.add(param, arg)
		          
		          val res = check(process)(nf)

		          // Restore nenv
		          nenv = backupNenv
		          penv.remove(nx)
		          res
		        case _ => throw IllFormedAst
          }
		    case MinimumFixpoint(x, params, f, args) =>
		      val (sf, nfFnsAux, pvars) = MinimumFixpoint(x, params, f, args).substitute(nenv)
		      sf match {
		        case MinimumFixpoint(nx, nparams, nf, nargs) =>
		          val nfFns = domainForm(nfFnsAux, pvars, penv)
		          val (template, marked) = argTemplate(nargs, nfFns, new Environment[String, String]())
		          val pset = Set[ProcessElt](new ProcessElt(process, marked))
		          penv.add(nx, (List((pset, template)), nf, nparams, nfFns, Min, 0))

		          // Mask nenv
		          val backupNenv = nenv
		          nenv = new Environment[String, String]()
		          for((param, arg) <- nparams.zip(nargs))
		            nenv.add(param, arg)
		          
		          val res = check(process)(nf)

		          // Restore nenv
		          nenv = backupNenv
		          penv.remove(nx)
		          res
		        case _ => throw IllFormedAst
          }
      }
      
      check(process)(prop)
    }

		
    val closure = env.allClosures.get(processId).get
    
    if(arguments.length != closure.signature.parameters.length)
      throw WrongArgumentCount(processId)
    
    if(showTrace)
      logger.log(closure.show)
      
    val process = Process(closure, arguments)
    
    if(showTrace)
      logger.log(process.show)
      
    val newProp = env.installDefprop(Nil)(prop)
    
    if(showTrace) {
      logger.logln("\n*** PROPERTY ***")
      logger.logln(prop.show)
      logger.logln("****************")
    }
    
    logger.log("\nProcessing...")
    checkCounter = 0
    
    val startTime = System.currentTimeMillis()
    val res = 
	    try {
		    val doCheck = future { check(process, prop) }
		    Await.result(doCheck, timeout)
	    } catch {
	      case _: TimeoutException =>
	        throw CheckerTimedOut(timeout)
    }
    val stopTime = System.currentTimeMillis()
    
    if(showTime)
      logger.logln("\n- Time elapsed: " + ((stopTime - startTime) / 1000) + " secs -")
      
    if(showCheckCounter)
      logger.logln("\n- Number of state visits: " + checkCounter + " -")
      
    // Log the result.
    val args = 
      arguments match {
        case Nil => ""
        case hd::tl => "(" + hd + tl.map("," + _) + ")"
      }
    
    if(res) {
      logger.logln("\n Process " + processId + args + " satisfies the formula " + prop.show)
    } else {
      logger.logln("\n Process " + processId + args + " does not satisfy the formula " + prop.show)
    }
    
    (res, logger.getLog)
    
  }
  
  private def createDomains(process: Process,
  													f: ModalLogic,
  													penv: Environment[String, (List[(Set[ProcessElt], List[String])], ModalLogic, List[String], List[String], Fixpoints, Int)],
  													nenv: Environment[String, String]): (List[String], List[String]) = {

		val (freeNamesAux, propVars) = f.freeNames(nenv)
    val supps = penv.mapValues(_._4)
    val freeNames = propVars.foldRight(freeNamesAux)({ 
      case (next, acc) => supps.getOrElse(next, Nil).filter(!acc.contains(_)) ++ acc
    })
    val fnp = process.freeNames()
    val domain = Namegen.freshAlias()::(fnp.filter(!freeNames.contains(_)) ++ freeNames)
    (domain, fnp)
  }
  
  private def argTemplate(args: List[String], supp: List[String], assocs: Environment[String, String]): (List[String], List[String]) = {
    args match {
      case Nil => (Nil, Nil)
      case hd :: tl =>
        val (l1, l2) = argTemplate(tl, supp, assocs)
        if (hd.contains(supp)) {
          (hd :: l1, l2)
        } else {
          val marker = assocs.getOrElse(hd, Namegen.generateBoundName())
          (marker :: l1, hd :: l2)
        }
    }
  }
  
  private def domainForm(l: List[String],
      									 pvarsL: List[String], 
      									 env: Environment[String, (List[(Set[ProcessElt], List[String])], ModalLogic, List[String], List[String], Fixpoints, Int)]): List[String] = {
    pvarsL match {
      case Nil => l
      case hd :: tl =>
        val res = domainForm(l, tl, env)
        try {
          val (_, _, _, supp, _, _) = env.find(hd)
          supp.filter(!res.contains(_)) ++ res
        } catch {
          case NotFound(_) => res
        }
    }
  }
  
}
