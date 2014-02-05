package biosimilarity.slmc.data

import Equation._
import scala.collection.mutable
import scala.collection.immutable._
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc.{Action => _, Test => _, Variable => _, Output => _, Input => _, _}
import biosimilarity.slmc.util.Monoid
import biosimilarity.slmc.ast.sr.Fail
import biosimilarity.slmc.util.Showable
import Closure._
import biosimilarity.slmc.util.Environment

case object NameClash extends Exception

case class Signature(val id: Variable, 
    								 val parameters: Parameters)

class Closure(val environment: Map[Variable, (FreeNames, Equation)],
        	  	val signature: Signature) extends Showable {
  
  def show(): String = {
    var res = ""
    val doneVars = new mutable.HashMap[Int, Int]()
      
    def showNfAux: List[Variable] => Unit = {
      case Nil => ;
      case hd::tl =>
        if(doneVars.contains(hd)) {
          showNfAux(tl)
        } else {
          doneVars.put(hd, 0)
          val eq = environment.get(hd).get._2
          res += "\n*** X" + hd + " ***\n"
          res += "******\n"
          showNfAux(eq.allVariables ++ tl)
        }
    }
      
    doneVars.put(Closure.voidEquationVariable, 0)
    res += "\n\n*** EQUATIONS ***"
    if(signature.id == Closure.voidEquationVariable) {
      res += "\n*** EMPTY ***\n"
    } else {
      showNfAux(List(signature.id))
    }
    res += "\n*****************\n"
    res
  }

}

object Closure {

  type Parameters = List[String]
  type FreeNames = List[String]
  
  private type PreAction = (ml.Label, Variable, List[String])
  private type PreTau = (Variable, List[String])
  private type PreTest = (TestType, String, String, Variable, List[String])
  
  private type History = List[(Any, Int, List[String], PiCalculus)]
  private type Promise = List[(Int, List[String], PiCalculus)]
  
  private var history: History = Nil
  private var promise: Promise = Nil
  
  def apply(processId: String, parameters: List[String], globalEnvironment: Map[String, (List[String], PiCalculus)]): Closure = {
    val equations = new Environment[Variable, Equation]()
    val start = freshEquationVariable()
    
    // Populate equations.
    promise = (start, parameters, pc.Variable(processId, parameters))::promise
    while(!promise.isEmpty) {
      val (id, parameters, definition) = promise.head
      promise = promise.tail
      val subEnvironment = new HashMap[String, String]()
      val normalEq = NormalEquation(subEnvironment, globalEnvironment, parameters)(definition)
      val (resActs, resTests, resTaus) = treatActions(normalEq.actions)
      val resSums = treatSums(normalEq.sums)
      equations.add(id, Equation(parameters, normalEq.restrictions, resActs, resTests, resTaus, resSums))
    }
    
    relevantNames(equations, start) // Stateful
    
    if(equations.find(start).actionCount == 0) {
      new Closure(environment = new HashMap[Variable, (FreeNames, Equation)](), 
          				signature = Signature(voidEquationVariable, parameters))
    } else {
      
      // Associate free names to equations
      val free = freeNames(equations, start)
      val signatures = free.map({ case (k,v) => (k, (v, equations.find(k))) })      
      
      new Closure(signatures.toMap, Signature(start, parameters))
    }
  }
  
  private def treatAction(arg: (PiCalculus, PiCalculus, List[String])): (Option[PreAction], Option[PreTest], Option[PreTau]) = {
    
    def returnAction(action: PreAction) = (Some(action), None, None)
    def returnTest(test: PreTest) = (None, Some(test), None)
    def returnTau(tau: PreTau) = (None, None, Some(tau))
      
    def treatAction: ((PiCalculus, PiCalculus, List[String])) => (Option[PreAction], Option[PreTest], Option[PreTau]) = {
      case (pc.Action(pc.Output(channel, arguments), process), continue, names) =>
        if(continue == Void) {
          returnAction((ml.Output(channel, arguments), voidEquationVariable, Nil))
        } else {
          val (finished, x, args) = visited(continue, process)(history)
          if(finished) {
            returnAction((ml.Output(channel, arguments), x, args))
          } else {
	          val fresh = freshEquationVariable()
	          history = (continue, fresh, names, process)::history
	          promise = (fresh, names, process)::promise
	          returnAction((ml.Output(channel, arguments), fresh, names))
          } 
        }
      case (pc.Action(pc.Input(channel, arguments), process), continue, names) =>
        if(continue == Void) {
          returnAction((ml.Input(channel, arguments), voidEquationVariable, Nil))
        } else {
          val (finished, x, args) = visited(continue, process)(history)
          if(finished) {
            returnAction((ml.Input(channel, arguments), x, args))
          } else {
	          val fresh = freshEquationVariable()
	          history = (continue, fresh, names, process)::history
	          promise = (fresh, names, process)::promise
	          returnAction((ml.Input(channel, arguments), fresh, names))
          } 
        }
      case (pc.Action(pc.Tau, process), continue, names) =>
        if(continue == Void) {
          returnTau((voidEquationVariable, Nil))
        } else {
          val (finished, x, args) = visited(continue, process)(history)
          if(finished) {
            returnTau((x, args))
          } else {
	          val fresh = freshEquationVariable()
	          history = (continue, fresh, names, process)::history
	          promise = (fresh, names, process)::promise
	          returnTau((fresh, names))
          }
        }
      case (pc.Test(id1, id2, process, pc.Equals), continue, names) =>
        if(continue == Void) {
          returnTest((Equals, id1, id2, voidEquationVariable, Nil))
        } else {
          val (finished, x, args) = visited(continue, process)(history)
          if(finished) {
            returnTest(Equals, id1, id2, x, args)
          } else {
	          val fresh = freshEquationVariable()
	          history = (continue, fresh, names, process)::history
	          promise = (fresh, names, process)::promise
	          returnTest(Equals, id1, id2, fresh, names)
          }
        }
      case (pc.Test(id1, id2, process, pc.Differs), continue, names) =>
        if(continue == Void) {
          returnTest((Differs, id1, id2, voidEquationVariable, Nil))
        } else {
          val (finished, x, args) = visited(continue, process)(history)
          if(finished) {
            returnTest(Differs, id1, id2, x, args)
          } else {
	          val fresh = freshEquationVariable()
	          history = (continue, fresh, names, process)::history
	          promise = (fresh, names, process)::promise
	          returnTest(Differs, id1, id2, fresh, names)
          }
        }
      case _ => (None, None, None)
    }
    
    treatAction(arg)
  }
    
  def treatActions(actsL: List[(PiCalculus, PiCalculus, List[String])]): (List[PreAction], List[PreTest], List[PreTau]) = {
    var treatedActs = for(act <- actsL) yield treatAction(act)
    val (acts, tests, taus) = treatedActs.reverse.unzip3
    (acts.flatten, tests.flatten, taus.flatten)
  }
  
  def treatSums: List[List[(PiCalculus, PiCalculus, List[String])]] => List[(List[PreAction], List[PreTest], List[PreTau])] =
    Monoid.extend(treatActions)
    
  private def visited[A, B](el: PiCalculus, c: PiCalculus) : History => (Boolean, Int, List[String]) = {
    case Nil => (false, voidEquationVariable, Nil)
    case (ptr, v, names, cont)::tl =>
      if(ptr == el) {
        try {
          (true, v, matchArgs(cont, names, c))
        } catch {
          case NameClash =>
            visited(el, c)(tl)
        }
      } else {
        visited(el, c)(tl)
      }
  }
    
  // To determine if two process asts are the same up to a determined substitution
  def matchArgs(c1: PiCalculus, n1: List[String], c2: PiCalculus): List[String] = {
    val oldArgs = new mutable.HashMap[String, Int]()
    val newArgs = Array.fill[String](n1.length)("")
    val bound = new Environment[String, Int]()
    
    def matchName(n1: String, n2: String) {
	    oldArgs.get(n1) match {
	      case Some(i) =>
	        if(!newArgs(i).equals("") && !newArgs(i).equals(n2)) {
	          throw NameClash
	        } else {
	          newArgs(i) = n2
	        }
	      case None =>
	        if(!bound.mem(n1) && !n1.equals(n2)) {
	          throw NameClash
	        }
	    }
	  }
    
    def matchNames(ns1: List[String], ns2: List[String]) {
      for((n1, n2) <- ns1.zip(ns2))
        matchName(n1, n2)
    }
    
    def matchArgs(c1: PiCalculus, c2: PiCalculus) {
	    (c1, c2) match {
	      case (Void, _) => ;
	      case (Parallel(p1, p2), Parallel(q1, q2)) =>
	        matchArgs(p1, q1)
	        matchArgs(p2, q2)
	      case (Sum(p1, p2), Sum(q1, q2)) =>
	        matchArgs(p1, q1)
	        matchArgs(p2, q2)
	      case (New(nl1, p), New(nl2, q)) =>
	        for(id <- nl1) { bound.add(id, 0)}
	        matchArgs(p, q)
	        for(id <- nl1) { bound.remove(id) }
	      case (pc.Action(t1, p), pc.Action(t2, q)) =>
	        (t1, t2) match {
	          case (pc.Output(s1, o1), pc.Output(s2, o2)) =>
	            matchName(s1, s2)
	            matchNames(o1, o2)
	            matchArgs(p, q)
	          case (pc.Input(s1, o1), pc.Input(s2, o2)) =>
	            matchName(s1, s2)
	            for(id <- o1) { bound.add(id, 0) }
	            matchArgs(p, q)
	            for(id <- o1) { bound.remove(id) }
	          case (Tau, Tau) =>
	            matchArgs(p, q)
	          case _ => throw Fail()
	        }
	      case (pc.Test(n1, n2, p, t1), pc.Test(m1, m2, q, t2)) =>
	        if(t1 != t2) { throw new Error() }
	        matchName(n1, m1)
	        matchName(n2, m2)
	        matchArgs(p, q)
	      case (pc.Variable(id1, al1), pc.Variable(id2, al2)) =>
	        matchNames(al1, al2)
	      case _ => throw Fail()
	    }
	  }
    
    for((id,i) <- n1.view.zipWithIndex) { oldArgs.put(id, i) }
    matchArgs(c1, c2)
    for((elt, i) <- newArgs.zipWithIndex) {
      newArgs(i) = if(elt.equals("")) { n1(i) } else { elt }
    }
    newArgs.toList
  }
  
    
  val voidEquationVariable = 0
  private var fresh = voidEquationVariable + 1
  private def freshEquationVariable(): Int = {
    val res = fresh
    fresh = fresh + 1
    res
  }
  
  // All that relevant name crap
  
  // To handle the relevant parameter identification procedure
  def relevantNames(sys: Environment[Variable, Equation], entry: Variable) {
    val relevantNames = new mutable.HashMap[Variable, Array[Boolean]]()
    createRelevantNames(sys, relevantNames, entry)
    val visited = new mutable.HashMap[Variable, Int]()
    while(markRelevantNames(sys, relevantNames.toMap, visited, entry)) {  visited.clear() }
    visited.clear()
    val eq = sys.find(entry)
    relevantNames.update(entry, Array.fill[Boolean](eq.parameterCount)(true))
    cleanupSys(sys, relevantNames.toMap, visited, entry)
  }
  
  def createRelevantNames(sys: Environment[Variable, Equation], 
        								  relevantNames: mutable.HashMap[Variable, Array[Boolean]], 
        									name: Variable) {
    if(name == voidEquationVariable || relevantNames.contains(name)) { return }

    val eq = sys.find(name)
    relevantNames.put(name, Array.fill[Boolean](eq.parameterCount)(false))

    for((_,_,_,cont,_) <- eq.freeOutputs)  { createRelevantNames(sys, relevantNames, cont) }
    for((_,_,_,cont,_) <- eq.boundOutputs) { createRelevantNames(sys, relevantNames, cont) }
    for((_,_,_,cont,_) <- eq.freeInputs)   { createRelevantNames(sys, relevantNames, cont) }
    for((_,_,_,cont,_) <- eq.boundInputs)  { createRelevantNames(sys, relevantNames, cont) }
    for((_,_,_,cont,_) <- eq.tests)        { createRelevantNames(sys, relevantNames, cont) }
    for((cont,_) <- eq.taus)               { createRelevantNames(sys, relevantNames, cont) }

    for((acts, tests, taus) <- eq.sums) {
      for((_,_,_,cont,_) <- acts)  { createRelevantNames(sys, relevantNames, cont) }
      for((cont,_) <- taus)        { createRelevantNames(sys, relevantNames, cont) }
      for((_,_,_,cont,_) <- tests) { createRelevantNames(sys, relevantNames, cont) }
    }
  }
  
  def markRelevantNames(sys: Environment[Variable, Equation],
                 relevantNames: Map[Variable, Array[Boolean]],
                 visited: mutable.HashMap[Variable, Int],
                 name: Variable): Boolean = {
    if(name == voidEquationVariable || visited.contains(name)) { return false }
    visited.put(name, 0)
    val marker = relevantNames.get(name).get
    val eq = sys.find(name)
    var changed = false
    for((_, sub, obj, cont, args) <- eq.freeOutputs) {
      val res1 = markName(marker)(sub)
      val res2 = markNames(marker)(obj)
      val res3 =
        if(cont != voidEquationVariable) {
          val marker2 = relevantNames.get(cont).get
          markArguments(marker, marker2, 0)(args)
        } else {
          false
        }
      changed = changed || res1 || res2 || res3
    }
    for((_,_, obj, cont, args) <- eq.boundOutputs) {
      val res1 = markNames(marker)(obj)
      val res2 =
        if(cont != voidEquationVariable) {
          val marker2 = relevantNames.get(cont).get
          markArguments(marker, marker2, 0)(args)
        } else {
          false
        }
      changed = changed || res1 || res2
    }
    for((_, sub, _, cont, args) <- eq.freeInputs) {
      val res1 = markName(marker)(sub)
      val res2 =
      if(cont != voidEquationVariable) {
        val marker2 = relevantNames.get(cont).get
        markArguments(marker, marker2, 0)(args)
      } else {
        false
      }
      changed = changed || res1 || res2
    }
    for((_,_,_, cont, args) <- eq.boundInputs) {
      val res =
        if(cont != voidEquationVariable) {
          val marker2 = relevantNames.get(cont).get
          markArguments(marker, marker2, 0)(args)
        } else {
          false
        }
      changed = changed || res
    }
    for((_, id1, id2, cont, args) <- eq.tests) {
      val res1 = markName(marker)(id1) || markName(marker)(id2)
      val res2 =
        if(cont != voidEquationVariable) {
          val marker2 = relevantNames.get(cont).get
          markArguments(marker, marker2, 0)(args)
        } else {
          false
        }
      changed = changed || res1 || res2
    }
    for((cont, args) <- eq.taus) {
      val res =
        if(cont != voidEquationVariable) {
          val marker2 = relevantNames.get(cont).get
          markArguments(marker, marker2, 0)(args)
        } else {
          false
        }
      changed = changed || res
    }
    for((acts, tests, taus) <- eq.sums) {
      for((t, sub, obj, cont, args) <- acts) {
        val res1 = markName(marker)(sub)
        val res2 =
          if(t == Output) {
            markNames(marker)(obj)
          } else {
            false
          }
        val res3 =
          if(cont != voidEquationVariable) {
            val marker2 = relevantNames.get(cont).get
            markArguments(marker, marker2, 0)(args)
          } else {
            false
          }
        changed = changed || res1 || res2 || res3
      }
      for((cont, args) <- taus) {
        val res =
	        if(cont != voidEquationVariable) {
	          val marker2 = relevantNames.get(cont).get
	          markArguments(marker, marker2, 0)(args)
	        } else {
	          false
	        }
        changed = changed || res
      }
      for((_, id1, id2, cont, args) <- tests) {
        val res1 = markName(marker)(id1) || markName(marker)(id2)
        val res2 =
          if(cont != voidEquationVariable) {
            val marker2 = relevantNames.get(cont).get
            markArguments(marker, marker2, 0)(args)
          } else {
            false
          }
        changed = changed || res1 || res2
      }
    }

    for((_,_,_, cont,_) <- eq.freeOutputs) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }
    for((_,_,_, cont,_) <- eq.boundOutputs) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }
    for((_,_,_, cont,_) <- eq.freeInputs) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }
    for((_,_,_, cont,_) <- eq.boundInputs) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }
    for((_,_,_, cont,_) <- eq.tests) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }
    for((cont,_) <- eq.taus) {
      changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
    }

    for((acts, tests, taus) <- eq.sums) {
      for((_,_,_, cont,_) <- acts) {
        changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
      }
      for((cont,_) <- taus) {
        changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
      }
      for((_,_,_, cont,_) <- tests) {
        changed = changed || markRelevantNames(sys, relevantNames, visited, cont)
      }
    }

    changed
  }
  
  // To identify the relevant parameters
  def markName(marker: Array[Boolean]): Name => Boolean = {
    case Parameter(i) =>
      if(!marker(i)) {
        marker(i) = true
        true
      } else { false }
    case _ => false
  }
  
  def markNames(marker: Array[Boolean]): List[Name] => Boolean = {
    case Nil => false
    case hd::tl => markName(marker)(hd) || markNames(marker)(tl)
  }
  
  def markArguments( marker1: Array[Boolean], marker2: Array[Boolean], i: Int): List[Name] => Boolean = {
    case Nil => false
    case hd::tl =>
      (marker2(i) && markName(marker1)(hd)) || markArguments(marker1, marker2, i+1)(tl)
  }
  
  def cleanupSys(sys: Environment[Variable, Equation],
                 relevantNames: Map[Variable, Array[Boolean]],
                 visited: mutable.HashMap[Variable, Int],
                 name: Variable) {
    // NOTE: predicate below is negated in translation to avoid wrapping the entire function
    if(name == voidEquationVariable || visited.contains(name)) { return } else { visited.put(name, 0) }

    val marker: Array[Boolean] = relevantNames.get(name).get
    val eq = sys.find(name)
    sys.remove(name)
    var pos: Int = -1
    val newParameters: Array[Int] = 
      marker.map({ b => if(b) { pos += 1; pos } else { -1 }})
    val newEq = cleanupEquation(newParameters, relevantNames, pos)(eq)
    sys.add(name, newEq)

    def recurse(x: Variable) { cleanupSys(sys, relevantNames, visited, x) }
    for((_,_,_, cont,_) <- eq.freeOutputs)  { recurse(cont) }
    for((_,_,_, cont,_) <- eq.boundOutputs) { recurse(cont) }
    for((_,_,_, cont,_) <- eq.freeInputs)   { recurse(cont) }
    for((_,_,_, cont,_) <- eq.boundInputs)  { recurse(cont) }
    for((_,_,_, cont,_) <- eq.tests)        { recurse(cont) }
    for(       (cont,_) <- eq.taus)         { recurse(cont) }

    for((acts, tests, taus) <- eq.sums) {
      for((_,_,_, cont,_) <- acts)    { recurse(cont) }
      for((_,_,_, cont,_) <- tests)   { recurse(cont) }
      for(       (cont,_) <- taus)    { recurse(cont) }
    }
  }
  
  def cleanupEquation(newParameters: Array[Int], relevantNames: Map[Variable, Array[Boolean]], parameterCount: Int)(eq: Equation): Equation = {
    val freeOutputs = Array.fill[Action](eq.freeOutputs.length)((Output, Free(""), Nil, voidEquationVariable, Nil))
    val boundOutputs = Array.fill[Action](eq.boundOutputs.length)((Output, Free(""), Nil, voidEquationVariable, Nil))
    val freeInputs = Array.fill[Action](eq.freeInputs.length)((Input, Free(""), Nil, voidEquationVariable, Nil))
    val boundInputs = Array.fill[Action](eq.boundInputs.length)((Input, Free(""), Nil, voidEquationVariable, Nil))
    val tests = Array.fill[Test](eq.tests.length)((Equals, Free(""), Free(""), voidEquationVariable, Nil))
    val taus = Array.fill[Tau](eq.taus.length)((voidEquationVariable, Nil))

    for(((t, sub, obj, cont, args), i) <- eq.freeOutputs.zipWithIndex) {
      val nsub = cleanupName(newParameters)(sub)
      val nobj = cleanupNames(newParameters)(obj)
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      freeOutputs(i) = (t, nsub, nobj, cont, nargs)
    }
    for(((t, sub, obj, cont, args), i) <- eq.boundOutputs.zipWithIndex) {
      val nsub = cleanupName(newParameters)(sub)
      val nobj = cleanupNames(newParameters)(obj)
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      boundOutputs(i) = (t, nsub, nobj, cont, nargs)
    }
    for(((t, sub, obj, cont, args), i) <- eq.freeInputs.zipWithIndex) {
      val nsub = cleanupName(newParameters)(sub)
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      freeInputs(i) = (t, nsub, obj, cont, nargs)
    }
    for(((t, sub, obj, cont, args), i) <- eq.boundInputs.zipWithIndex) {
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      boundInputs(i) = (t, sub, obj, cont, nargs)
    }
    for(((typ, id1, id2, cont, args), i) <- eq.tests.zipWithIndex) {
      val (nid1, nid2) = (cleanupName(newParameters)(id1), cleanupName(newParameters)(id2))
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      tests(i) = (typ, nid1, nid2, cont, nargs)
    }
    for(((cont, args), i) <- eq.taus.zipWithIndex) {
      val nargs =
        if(cont != voidEquationVariable) {
          val marker = relevantNames.get(cont).get
          cleanupArguments(marker, newParameters, 0)(args)
        } else {
          Nil
        }
      taus(i) = (cont, nargs)
    }

    val sums = eq.sums.map((sum) =>
      sum match { case (acts, tests, taus) =>
        val newActs = acts.map(act =>
          act match { case (t, sub, obj, cont, args) =>
            val nsub = cleanupName(newParameters)(sub)
            val nobj =
              if(t == Output) {
                cleanupNames(newParameters)(obj)
              } else {
                obj
              }
            val nargs =
              if(cont != voidEquationVariable) {
                val marker = relevantNames.get(cont).get
                cleanupArguments(marker, newParameters, 0)(args)
              } else {
                Nil
              }
            (t, nsub, nobj, cont, nargs)
          })

        val newTaus = taus.map(tau =>
          tau match { case (cont, args) =>
            val nargs =
              if(cont != voidEquationVariable) {
                val marker = relevantNames.get(cont).get
                cleanupArguments(marker, newParameters, 0)(args)
              } else {
                Nil
              }
            (cont, nargs)
          })
        val newTests = tests.map(test =>
          test match { case (typ, id1, id2, cont, args) =>
            val (nid1, nid2) = (cleanupName(newParameters)(id1), cleanupName(newParameters)(id2))
            val nargs =
              if(cont != voidEquationVariable) {
                val marker = relevantNames.get(cont).get
                cleanupArguments(marker, newParameters, 0)(args)
              } else {
                Nil
              }
            (typ, nid1, nid2, cont, nargs)
          })
        (newActs, newTests, newTaus)
      })

    new Equation(parameterCount = eq.parameterCount,
                 restrictionCount = eq.restrictionCount,
                 freeInputs = freeInputs.toList,
                 freeOutputs = freeOutputs.toList,
                 boundInputs = boundInputs.toList,
                 boundOutputs = boundOutputs.toList,
                 tests = tests.toList,
                 taus = taus.toList,
                 sums = sums)
  }

  def cleanupName(newParameters: Array[Int]): Name => Name = {
    case Parameter(i) => Parameter(newParameters(i))
    case name => name
  }

  def cleanupNames(newParameters: Array[Int]): List[Name] => List[Name] = 
    Monoid.extend(cleanupName(newParameters))
    
  def cleanupArguments(marker: Array[Boolean], newParameters: Array[Int], i: Int): List[Name] => List[Name] = {
    case Nil => Nil
    case hd::tl =>
      if(marker(i)) {
        cleanupName(newParameters)(hd)::cleanupArguments(marker, newParameters, i+1)(tl)
      } else {
        cleanupArguments(marker, newParameters, i+1)(tl)
      }
  }
  
  def freeNames(sys: Environment[Variable, Equation], entry: Variable): mutable.HashMap[Variable, List[String]] = {
    val freeNames = new mutable.HashMap[Variable, List[String]]()
    createFreeNames(sys, freeNames, entry)
    var notDone = true
    val visited = new mutable.HashMap[Variable, Int]()
    while(markFree(sys, freeNames, visited, entry)) {
      visited.clear()
    }
    visited.clear()
    freeNames
  }

  def createFreeNames(sys: Environment[Variable, Equation], freeNames: mutable.HashMap[Variable, List[String]], name: Variable) {
    if(name == voidEquationVariable || freeNames.contains(name)) { return }
    val eq = sys.find(name)
    var freeNameList: List[String] = Nil
    freeNames.put(name, freeNameList)

    def mark(nL: List[Name]) { freeNameList = markFreeNames(freeNameList)(nL)}
    def recurse(cont: Variable) { createFreeNames(sys, freeNames, cont) }
    def markAndRecurse(nL: List[Name], cont: Variable) { mark(nL); recurse(cont) }

    for((_, sub, obj, cont, args) <- eq.freeOutputs)  { markAndRecurse(sub::obj ++ args, cont) }
    for((_,   _, obj, cont, args) <- eq.boundOutputs) { markAndRecurse(     obj ++ args, cont) }
    for((_, sub,   _, cont, args) <- eq.freeInputs)   { markAndRecurse(sub::       args, cont) }
    for((_,   _,   _, cont, args) <- eq.boundInputs)  { markAndRecurse(            args, cont) }
    for((_, id1, id2, cont, args) <- eq.tests)        { markAndRecurse(id1::id2 :: args, cont) }
    for(             (cont, args) <- eq.taus)         { markAndRecurse(            args, cont) }

    for((acts, tests, taus) <- eq.sums) {
      for((t, sub, obj, cont, args) <- acts) {
        if(t == Output)                         { markAndRecurse(sub::obj ++ args, cont) }
        else                                    { markAndRecurse(sub::       args, cont) } }
      for(             (cont, args) <- taus)    { markAndRecurse(            args, cont) }
      for((_, id1, id2, cont, args) <- tests)   { markAndRecurse(List(id1, id2)  , cont) }
    }    
    freeNames.put(name, freeNameList)
  }
  
  def markFreeName(l: List[String]): Name => List[String] = {
    case Free(s) =>
      if(l.contains(s)) {
        s::l
      } else {
        l
      }
    case _ => l
  }
  
  def markFreeNames(l: List[String])(nL: List[Name]): List[String] = {
    nL.foldLeft(l)((acc, n) => markFreeName(acc)(n))
  }

  def markFree[A](sys: Environment[Variable, Equation],
                  freeNames: mutable.HashMap[Variable, List[A]],
                  visited: mutable.HashMap[Variable, Int], 
                  name: Int): Boolean = {
    // NOTE: predicate below is negated in translation to avoid wrapping the entire function
    if(name == voidEquationVariable || freeNames.contains(name)) { return false }
    visited.put(name, 0)
    val fnL = freeNames.get(name).get
    val eq = sys.find(name)
    var changed = false

    def change[A](cont: Int): Boolean = {
      if(cont == voidEquationVariable) {
         false
      } else{
        val (res, newCont) = markContinuation(freeNames.get(cont).get, fnL)
        freeNames.put(cont, newCont)
        res
      }
    }

    for((_,_,_, cont,_) <- eq.freeOutputs) { changed = changed || change(cont) }
    for((_,_,_, cont,_) <- eq.boundOutputs) { changed = changed || change(cont) }
    for((_,_,_, cont,_) <- eq.freeInputs) { changed = changed || change(cont) }
    for((_,_,_, cont,_) <- eq.boundInputs) { changed = changed || change(cont) }
    for((_,_,_, cont,_) <- eq.tests)  { changed = changed || change(cont) }
    for(      (cont, _) <- eq.taus)   { changed = changed || change(cont) }

    for((acts, tests, taus) <- eq.sums) {
      for((_,_,_, cont,_) <- acts)    { changed = changed || change(cont)}
      for(       (cont,_) <- taus)    { changed = changed || change(cont) }
      for((_,_,_, cont,_) <- tests)   { changed = changed || change(cont) }
    }

    changed
  }
  
  def markContinuation[A](l1: List[A], l2: List[A]): (Boolean, List[A]) = {
    var res = false
    def markContinuation[A](l2: List[A]): List[A] => List[A] = {
      case Nil => l2
      case hd::tl =>
        if(l2.contains(hd)) {
          markContinuation(l2)(tl)
        } else {
          res = true
          markContinuation(hd::l2)(tl)
        }
    }
    (res, markContinuation(l2)(l1))
  }
  
}

























