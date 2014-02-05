package biosimilarity.slmc

import biosimilarity.slmc.ast.ss.SLMCStatement
import scala.collection.mutable
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc.{ PiCalculus }
import biosimilarity.slmc.ast.cc
import biosimilarity.slmc.ast.cc.{ ConversationCalculus }
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.ml.{ ModalLogic }
import biosimilarity.slmc.data.Closure
import biosimilarity.slmc.util.Environment
import biosimilarity.slmc.ast.sr.WrongArgumentCount
import biosimilarity.slmc.util.OCaml.NotFound
import biosimilarity.slmc.ast.sr.UndeclaredIdentifier
import biosimilarity.slmc.ast.sr.WrongArguments
import biosimilarity.slmc.ast.sr.IllFormedAst
import biosimilarity.slmc.util.Logger

/** The SLMC Process environment */
class SLMC private(val processDecs: Map[String, (List[String], PiCalculus)],
    							 val mrProcesses: List[(String, (List[String], List[List[String]], List[PiCalculus]))],
    							 val ccProcesses: List[(String,  List[String], ConversationCalculus)],
    							 val formulaDecs: Map[String, (List[String], List[String], ModalLogic)],
    							 val allFormulas: List[(String, List[String], List[String], ModalLogic)],
    							 val allClosures: Map[String, Closure]) {

  def this() = this(processDecs = Map(),
      							mrProcesses = Nil,
      							ccProcesses = Nil,
      							formulaDecs = Map(),
      							allFormulas = Nil,
      							allClosures = Map())
      							
  /** installs a conversation calculus by converting it to a pi calculus and storing both. */
  def installConversationCalculus(name: String, parameters: List[String], process: ConversationCalculus): SLMC = {
    
    // Convert to PiCalculus
    val piAst = PiCalculus("up", "here", pc.Variable(name, "up" :: "here" :: parameters))(process)
    
    // Add the PiCalculus to the system
    val newSLMC = installPiProcesses(List(name), List("up" :: "here" :: parameters), List(piAst))

    // Add the ConversationCalculus to the system
    val newCCProcesses = (name, parameters, process)::ccProcesses
    new SLMC(processDecs = newSLMC.processDecs,
             mrProcesses = newSLMC.mrProcesses,
             ccProcesses = newCCProcesses,
      			 formulaDecs = newSLMC.formulaDecs,
      			 allFormulas = newSLMC.allFormulas,
             allClosures = newSLMC.allClosures)
  }
  
  /** installs a set of mutually recursive pi processes. */
  def installPiProcesses(names: List[String], parameterss: List[List[String]], processes: List[PiCalculus]): SLMC = {

    // Add the new process declarations
    val newProcessDecs = processDecs ++ names.zip(parameterss.zip(processes))

    // Check the new processes for unguarded recursion (throws UnguardedRecursion, UndeclaredIdentifier)
    names.foreach(name => newProcessDecs.get(name).get._2.checkForUnguardedRecursion(newProcessDecs, name, Nil))
    
    // Convert the processes to closures.
    val closures = names.zip(parameterss).map({ case (id, parameters) => Closure(id, parameters, newProcessDecs) })
    
    // Add the closures to closures.
    val newClosures = allClosures ++ names.zip(closures)
    
    // Update mrProcesses.
    val newMRProcesses = (names.head, (names, parameterss, processes))::mrProcesses
    
    new SLMC(processDecs = newProcessDecs,
        		 mrProcesses = newMRProcesses,
        		 ccProcesses = ccProcesses,
        		 formulaDecs = formulaDecs,
        		 allFormulas = allFormulas,
        		 allClosures = newClosures)
  }
  
  def installProposition(id: String, nparams: List[String], pparams: List[String], prop: ModalLogic): SLMC = {
    val res = installDefprop(pparams)(prop)
    val newFormulaDecs = formulaDecs + ((id, (nparams, pparams, res)))
    val newAllFormulas = (id, nparams, pparams, prop)::allFormulas
    new SLMC(processDecs = processDecs,
        		 mrProcesses = mrProcesses,
        		 ccProcesses = ccProcesses,
        		 formulaDecs = newFormulaDecs,
        		 allFormulas = newAllFormulas,
        		 allClosures = allClosures)
  }
  
  /** Auxiliary functions to installProposition */
  object PropVar {
    private val pvInit = "#X"
    private var pvCount = 0
	  def freshPvar() = {
	    val res = pvInit + pvCount
	    pvCount += 1
	    res
	  }
  }
  import PropVar._
  
  def installDefprop(pparams: List[String]): ModalLogic => ModalLogic = {
    val ph = new Environment[String, Int]()
    pparams.foreach(ph.add(_,0))
    
    def installDefprop: ModalLogic => ModalLogic = {
	    
			def extractArgs(args: List[ModalLogic], i: Int, len1: Int, len2: Int): (List[String], List[ModalLogic]) = {
		    args match {
		      case Nil =>
		        if (i != len1 + len2) {
		          throw WrongArgumentCount("unknown")
		        } else {
		          (Nil, Nil)
		        }
		      case ml.Abbreviate(s, args) :: tl =>
		        val (r1, r2) = extractArgs(tl, (i + 1), len1, len2)
		        if (i < len1) {
		          if (args.length > 0) {
		            throw WrongArguments("Wrong kind of argument!")
		          } else {
		            (s :: r1, r2)
		          }
		        } else {
		          (r1, ml.Abbreviate(s, args) :: r2)
		        }
		      case hd :: tl =>
		        if (i < len1) {
		          throw WrongArguments("Wrong kind of argument!")
		        } else {
		          val (r1, r2) = extractArgs(tl, i + 1, len1, len2)
		          (r1, hd :: r2)
		        }
		    }
		  }
			
			import biosimilarity.slmc.ast.ml._
		  
	    _ match {
	      case True => True
	      case False => False
	      case ml.Void => ml.Void
	      case Compare(i, t) => Compare(i, t)
	      case Equal(id1, id2) => Equal(id1, id2)
	      case NotEqual(id1, id2) => NotEqual(id1, id2)
	      case Not(f) => Not(installDefprop(f))
	      case And(f1, f2) => And(installDefprop(f1), installDefprop(f2))
	      case Or(f1, f2) => Or(installDefprop(f1), installDefprop(f2))
	      case Implies(f1, f2) =>
	        Implies(installDefprop(f1), installDefprop(f2))
	      case Equivalent(f1, f2) =>
	        Equivalent(installDefprop(f1), installDefprop(f2))
	      case Decompose(f1, f2) =>
	        Decompose(installDefprop(f1), installDefprop(f2))
	      case Compose(f1, f2) =>
	        Compose(installDefprop(f1), installDefprop(f2))
	      case Reveal(s, f) => Reveal(s, installDefprop(f))
	      case RevealAll(s, f) => RevealAll(s, installDefprop(f))
	      case Fresh(s, f) => Fresh(s, installDefprop(f))
	      case Free(s) => Free(s)
	      case Hidden(s, f) => Hidden(s, installDefprop(f))
	      case MayTau(f) => MayTau(installDefprop(f))
	      case AllTau(f) => AllTau(installDefprop(f))
	      case MayLabelled(l, f) => MayLabelled(l, installDefprop(f))
	      case AllLabelled(l, f) => AllLabelled(l, installDefprop(f))
	      case MayOutputN(n, f) => MayOutputN(n, installDefprop(f))
	      case MayInputN(n, f) => MayInputN(n, installDefprop(f))
	      case AllOutputN(n, f) => AllOutputN(n, installDefprop(f))
	      case AllInputN(n, f) => AllInputN(n, installDefprop(f))
	      case MayOutput(f) => MayOutput(installDefprop(f))
	      case MayInput(f) => MayInput(installDefprop(f))
	      case AllOutput(f) => AllOutput(installDefprop(f))
	      case AllInput(f) => AllInput(installDefprop(f))
	      case MayN(n, f) => MayN(n, installDefprop(f))
	      case AllN(n, f) => AllN(n, installDefprop(f))
	      case May(f) => May(installDefprop(f))
	      case All(f) => All(installDefprop(f))
	      case Exists(n, f) => Exists(n, installDefprop(f))
	      case ForAll(n, f) => ForAll(n, installDefprop(f))
	      case MaximumFixpoint(x, params, f, args) =>
	        if (params.length != args.length) {
	          throw WrongArgumentCount(x)
	        }
	        ph.add(x, params.length)
	        val res = installDefprop(f)
	        ph.remove(x)
	        MaximumFixpoint(x, params, res, args)
	      case MinimumFixpoint(x, params, f, args) =>
	        if (params.length != args.length) {
	          throw WrongArgumentCount(x)
	        }
	        ph.add(x, params.length)
	        val res = installDefprop(f)
	        ph.remove(x)
	        MinimumFixpoint(x, params, res, args)
	      case Eventually(f) => Eventually(installDefprop(f))
	      case Always(f) => Always(installDefprop(f))
	      case Inside(f) => Inside(installDefprop(f))
	      case ShowFails(f) => ShowFails(installDefprop(f))
	      case ShowSucceeds(f) => ShowSucceeds(installDefprop(f))
	      case PropositionVariable(p, args) =>
	        val npars =
	          try {
	            ph.find(p)
	          } catch {
	            case NotFound(_) => throw UndeclaredIdentifier(p)
	          }
	        if (npars != args.length) {
	          throw WrongArgumentCount(p)
	        } else {
	          PropositionVariable(p, args)
	        }
	      case Abbreviate(id, args) =>
	        try {
	          val (nparams, pparams, f) = formulaDecs.get(id).get
	          val (nargs, pargs) = extractArgs(args, 0, nparams.length, pparams.length)
	          installForm(Map(nparams.zip(nargs): _*), Map(pparams.zip(pargs): _*))(f)
	        } catch {
	          case NotFound(_) => throw UndeclaredIdentifier(id)
	          case WrongArguments(x) => throw WrongArguments(id + ": " + x)
	        }
	    }
	  }
    installDefprop
  }
  
  private def installForm(n: Map[String, String], p: Map[String, ModalLogic]): ModalLogic => ModalLogic = {
    val nh = new Environment[String, String]()
    val ph = new Environment[String, ModalLogic]()
    for((k,v) <- n) { nh.add(k,v) }
    for((k,v) <- p) { ph.add(k,v) }
    
  	import biosimilarity.slmc.ast.ml._
  	
	  def installList(l: List[String]): List[String] = {
	    l match {
	      case Nil => Nil
	      case hd :: tl =>
	        if (hd.equals("_")) {
	          hd :: installList(tl)
	        } else {
	          try {
	            val r = nh.find(hd)
	            r :: (installList(tl))
	          } catch {
	            case NotFound(_) => hd :: installList(tl)
	          }
	        }
	    }
	  }
	
	  def installLab(l: Label): Label = {
	    l match {
	      case ml.Output(s, sl) =>
	        val ns =
	          try {
	            nh.find(s)
	          } catch {
	            case NotFound(_) => s
	          }
	        ml.Output(ns, installList(sl))
	      case ml.Input(s, sl) =>
	        val ns =
	          try {
	            nh.find(s)
	          } catch {
	            case NotFound(_) => s
	          }
	        ml.Input(ns, installList(sl))
	    }
	  }
  	
  	def installForm: ModalLogic => ModalLogic = {
      case True => True
      case False => False
      case ml.Void => ml.Void
      case Compare(i, t) => Compare(i, t)
      case Equal(id1, id2) =>
        val nid1 = nh.getOrElse(id1, id1)
        val nid2 = nh.getOrElse(id2, id2)
        Equal(nid1, nid2)
      case NotEqual(id1, id2) =>
        val nid1 = nh.getOrElse(id1, id1)
        val nid2 = nh.getOrElse(id2, id2)
        NotEqual(nid1, nid2)
      case Not(f) => 
        Not(installForm(f))
      case And(f1, f2) =>
        And(installForm(f1), installForm(f2))
      case Or(f1, f2) =>
        Or(installForm(f1), installForm(f2))
      case Implies(f1, f2) =>
        Implies(installForm(f1), installForm(f2))
      case Equivalent(f1, f2) =>
        Equivalent(installForm(f1), installForm(f2))
      case Decompose(f1, f2) =>
        Decompose(installForm(f1), installForm(f2))
      case Compose(f1, f2) =>
        Compose(installForm(f1), installForm(f2))
      case Reveal(s, f) =>
        val ns = nh.getOrElse(s, s)
        Reveal(ns, installForm(f))
      case RevealAll(s, f) =>
        val ns = nh.getOrElse(s, s)
        RevealAll(ns, installForm(f))
      case Hidden(s, f) =>
        nh.add(s, s)
        val res = installForm(f)
        nh.remove(s)
        Hidden(s, res)
      case Fresh(s, f) =>
        nh.add(s, s)
        val res = installForm(f)
        nh.remove(s)
        Fresh(s, res)
      case Free(s) =>
        val ns = nh.getOrElse(s, s)
        Free(ns)
      case MayTau(f) => MayTau(installForm(f))
      case AllTau(f) => AllTau(installForm(f))
      case MayLabelled(l, f) => MayLabelled((installLab(l)), installForm(f))
      case AllLabelled(l, f) => AllLabelled((installLab(l)), installForm(f))
      case MayOutputN(n, f) =>
        val nn = nh.getOrElse(n, n)
        MayOutputN(nn, installForm(f))
      case MayInputN(n, f) =>
        val nn = nh.getOrElse(n, n)
        MayInputN(nn, installForm(f))
      case AllOutputN(n, f) =>
        val nn = nh.getOrElse(n, n)
        AllOutputN(nn, installForm(f))
      case AllInputN(n, f) =>
        val nn = nh.getOrElse(n, n)
        AllInputN(nn, installForm(f))
      case MayOutput(f) => MayOutput(installForm(f))
      case MayInput(f) => MayInput(installForm(f))
      case AllOutput(f) => AllOutput(installForm(f))
      case AllInput(f) => AllInput(installForm(f))
      case MayN(n, f) =>
        val nn = nh.getOrElse(n, n)
        MayN(nn, installForm(f))
      case AllN(n, f) =>
        val nn = nh.getOrElse(n, n)
        AllN(nn, installForm(f))
      case May(f) => May(installForm(f))
      case All(f) => All(installForm(f))
      case Exists(n, f) =>
        nh.add(n, n)
        val res = installForm(f)
        nh.remove(n)
        Exists(n, res)
      case ForAll(n, f) =>
        nh.add(n, n)
        val res = installForm(f)
        nh.remove(n)
        ForAll(n, res)
      case MaximumFixpoint(x, params, f, args) =>
        val fpv = freshPvar()
        ph.add(x, PropositionVariable(fpv, Nil))
        params.foreach(id => nh.add(id, id))
        val res = installForm(f)
        params.foreach(nh.remove(_))
        ph.remove(x)
        MaximumFixpoint(fpv, params, res, installList(args))
      case MinimumFixpoint(x, params, f, args) =>
        val fpv = freshPvar()
        ph.add(x, PropositionVariable(fpv, Nil))
        params.foreach(id => nh.add(id, id))
        val res = installForm(f)
        params.foreach(nh.remove(_))
        ph.remove(x)
        MinimumFixpoint(fpv, params, res, installList(args))
      case Eventually(f) => Eventually(installForm(f))
      case Always(f) => Always(installForm(f))
      case Inside(f) => Inside(installForm(f))
      case ShowFails(f) => ShowFails(installForm(f))
      case ShowSucceeds(f) => ShowSucceeds(installForm(f))
      case PropositionVariable(p, args) =>
        try {
          val res = ph.find(p)
          res match {
            case PropositionVariable(pvarname, pvarargs) =>
              if (args.length > 0) {
                PropositionVariable(pvarname, installList(args))
              } else {
                res
              }
            case _ => res
          }
        } catch {
          case NotFound(_) => throw IllFormedAst
        }
      case Abbreviate(id, args) => throw IllFormedAst
    }
  	installForm
  }
  
  private def intercalate(sep: String): List[String] => String = {
    case Nil => ""
    case hd::tl =>
      hd + tl.map(sep + _)
  }
  
    /** Prints a process to stdout given it's identifier */
  def showProcess(id: String): String = {
    val logger = new Logger()
    
	  def printProcAux(idProc: String, l: List[(String, (List[String], List[List[String]], List[PiCalculus]))]): Boolean = {
		  def printProcAnds(idProc: String, idL: List[String], paramL: List[List[String]], pL: List[PiCalculus]): Boolean = {
		    idL match {
		      case Nil => false
		      case hd :: tl =>
		        if (hd.equals(idProc)) {
		          logger.log("\ndefproc " + hd)
		          if (paramL.head.length > 0) {
		            logger.log("(" + intercalate(",")(paramL.head) + ")")
		          }
		          logger.log(" = ")
		          logger.logln(pL.head.show)
		          true
		        } else {
		          printProcAnds(idProc, tl, paramL.tail, pL.tail)
		        }
		    }
		  }
	    l match {
	      case Nil => false
	      case (id, (ids, params, ps)) :: tl =>
	        if (id.equals(idProc)) {
	          logger.log("\ndefproc " + id)
	          if (params.head.length > 0) {
	            logger.log("(" + intercalate(",")(params.head) + ")")
	          }
	          logger.log(" = ")
	          logger.logln(ps.head.show)
	          true
	        } else {
	          if (printProcAnds(idProc, ids.tail, params.tail, ps.tail)) {
	            true
	          } else {
	            printProcAux(idProc, tl)
	          }
	        }
	    }
	  }
    if(printProcAux(id, mrProcesses)) {
      logger.getLog
    } else {
      "Not found!"
    }
  }
  
  def showProcesses(): String = {
    val logger = new Logger    
    mrProcesses.map(_._1).foreach(id => logger.logln(showProcess(id)))
    logger.getLog
  }

  def showProposition(idForm: String): String = {
    val logger = new Logger
    def showProposition: List[(String, List[String], List[String], ModalLogic)] => Boolean = {
      case Nil => false
      case (id, ns, ps, form) :: tl =>
        if (id.equals(idForm)) {
          logger.log("\ndefprop " + id)
          if (ns.length > 0 || ps.length > 0) {
            logger.log("(" + intercalate(",")(ns))
            if (ns.length > 0 && ps.length > 0) {
              logger.log(", ")
            }
            logger.log(intercalate(",")(ps) + ")")
          }
          println(" = " + form.show)
          true
        } else {
          showProposition(tl)
        }
    }
    if(showProposition(allFormulas)) {
      logger.getLog
    } else {
      "Not found!"
    }
  }
  
  def showPropositions(): String = {
    val logger = new Logger
    allFormulas.map(_._1).foreach(id => logger.logln(showProposition(id)))
    logger.getLog
  }

}