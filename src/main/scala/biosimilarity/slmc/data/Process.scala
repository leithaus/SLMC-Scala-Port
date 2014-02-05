package biosimilarity.slmc.data

import scala.collection.mutable.HashMap
import scala.util.hashing.Hashing
import Process._
import component.{Error => _, Name => _, Input => _, Free => _, Bound => _, _}
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.util.Monoid
import biosimilarity.slmc.util.Namegen._
import biosimilarity.slmc.util.OCaml._
import biosimilarity.slmc.util.Printable
import biosimilarity.slmc.data.component.ActK
import biosimilarity.slmc.data.Equation._
import biosimilarity.slmc.ast.sr.Fail



/**
 * A process is a list of components, a system of equations, and a set of free names.
 */
class Process(val components: List[Component],
              val environment: Map[Variable, (List[String], Equation)]) extends Printable {
  
  def this() = {
    this(List(new Component), Map[Variable, (List[String], Equation)]())
  }

  def countComponents(): Int = components.length
  
  def countActions(): Int = {
    components.foldLeft(0)((acc, comp) => acc + comp.countActs())
  }

  // Note: This is a new helper function for findFnTau and findBnTau
  def getTau(eqFnType: Boolean, actionType: IO, componentIndex: Int, index: Int): Option[Either[TopAction, (TopAction, TopSum)]] = {
    try {
      val component = components(componentIndex)
      val acts1 =
        (eqFnType, actionType) match {
          case (true, Input) => component.freeInputs
          case (true, Output) => component.freeOutputs
          case (false, Input) => component.boundInputs
          case (false, Output) => component.boundOutputs
        }
      if(index < acts1.length) {
        return Some(Left(acts1(index)))
      } else {
        // Note: for some sadistic reason, we're indexing sums from the top of acts1.length
        // Also, we have to return the sum with the act so that find can check them for equality.
        val acts2: Seq[(TopAction, TopSum)] =
          component.actSums.flatMap((sum) => sum.acts.map((act) => (act, sum)))
          return Some(Right(acts2(index - acts1.length)))
      }
    } catch { case _: Throwable => None }
  }

    // Determines if a process is empty
  def isEmpty(): Boolean = {
    countComponents() == 1 &&
    components(0).countRestrictions == 0 &&
    components(0).nfreeOutputs == 0 &&
    components(0).nfreeInputs == 0 &&
    components(0).nboundOutputs == 0 &&
    components(0).nboundInputs == 0 &&
    components(0).ntests == 0 &&
    components(0).ntaus == 0 &&
    components(0).nsums == 0
  }

  // Returns the set of free names of a process
  def freeNames(): List[String] = {
    val h = new HashMap[String, Int]()
    val res: Ref[List[String]] = new Ref(Nil)
    for(comp <- components) {
      for(fnOut <- comp.freeOutputs) {
        freeName(fnOut.subject, h, res)
        freeNameL(fnOut.objects, h, res)
        freeNameL(fnOut.arguments, h, res)
        fnEqs(fnOut.continuation, h, res)
      }
      for(fnInp <- comp.freeInputs) {
        freeName(fnInp.subject, h, res)
        freeNameL(fnInp.arguments, h, res)
        fnEqs(fnInp.continuation, h, res)
      }
      for(bnOut <- comp.boundOutputs) {
        freeNameL(bnOut.objects, h, res)
        freeNameL(bnOut.arguments, h, res)
        fnEqs(bnOut.continuation, h, res)
      }
      for(bnInp <- comp.boundInputs) {
        freeNameL(bnInp.objects, h, res)
        fnEqs(bnInp.continuation, h, res)
      }
      for(test <- comp.idTests) {
        freeName(test.idl, h, res)
        freeName(test.idr, h, res)
        freeNameL(test.tArgs, h, res)
        fnEqs(test.tCont, h, res)
      }
      for(tau <- comp.actTaus) {
        freeNameL(tau.tauArgs, h, res)
        fnEqs(tau.tauCont, h, res)
      }
      for(TopSum(acts, taus, tests) <- comp.actSums) {
        for(act <- acts) {
          freeName(act.subject, h, res)
          if(act.actionType == Output) { freeNameL(act.objects, h, res) }
          freeNameL(act.arguments, h, res)
          fnEqs(act.continuation, h, res)
        }
        for(tau <- taus) {
          freeNameL(tau.tauArgs, h, res)
          fnEqs(tau.tauCont, h, res)
        }
        for(test <- tests) {
          freeName(test.idl, h, res)
          freeName(test.idr, h, res)
          freeNameL(test.tArgs, h, res)
          fnEqs(test.tCont, h, res)
        }
      }
    }
    !res
  }

  def fnEqs(c: Variable, h: HashMap[String, Int], res: Ref[List[String]]) {
    try { fnEqsAux(environment.get(c).get._1, h, res) } catch { case NotFound(_) => ; }
  }
  
    // Returns the different number of arguments of communications in a given name
  def getNumArgs(n: String): List[Int] = {
    var res: List[Int] = Nil
    for(comp <- components) {
      for(fnInp <- comp.freeInputs) {
        val len = fnInp.objects.length
        if(fnInp.subject.s.equals(n) && !res.contains(len)) {
          res = len::res
        }
      }
      for(TopSum(acts,_,_) <- comp.actSums) {
        for(inp <- acts) {
          val len = inp.objects.length
          if(inp.actionType == Internal && inp.isFnAct() && inp.subject.s.equals(n) && !res.contains(len)) {
            res = len::res
          }
        }
      }
    }
    res
  }
  
    // Tests if a process has a determined free name
  def testFreeName(n: String): Boolean = {
    var res = false
    
    for(comp <- components if !res) {
      for(fnOut <- comp.freeOutputs if !res) {
        res = testFnAux(fnOut, n, true)
        res = res || (try { environment.get(fnOut.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(fnInp <- comp.freeInputs if !res) {
        res = testFnAux(fnInp, n, true)
        res = res || (try { environment.get(fnInp.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(bnOut <- comp.boundOutputs if !res) {
        res = testFnAux(bnOut, n, true)
        res = res || (try {  environment.get(bnOut.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(bnInp <- comp.boundInputs if !res) {
        res = testFnAux(bnInp, n, true)
        res = res || (try { environment.get(bnInp.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(test <- comp.idTests if !res) {
        res = testFnName(test.idl, n)
        res = res || testFnName(test.idr, n)
        res = res || testFnNameL(test.tArgs, n)
        res = res || (try { environment.get(test.tCont).get._1.contains(n) } catch { case NotFound(_) => false })
      }
      for(tau <- comp.actTaus if !res) {
        res = testFnNameL(tau.tauArgs, n)
        res = res || (try { environment.get(tau.tauCont).get._1.contains(n) } catch { case NotFound(_) => false })
      }
      for(TopSum(acts, taus, tests) <- comp.actSums if !res){
        for(act <- acts if !res) {
          res = res || testFnAux(act, n, true)
          res = res || (try { environment.get(act.continuation).get._1.contains(n) } catch { case NotFound(_) => false })
        }
        for(tau <- taus if !res) {
          res = res || testFnNameL(tau.tauArgs, n)
          res = res || (try { environment.get(tau.tauCont).get._1.contains(n) } catch { case NotFound(_) => false } )
        }
        for(test <- tests if !res) {
          res = testFnName(test.idl, n)
          res = res || testFnName(test.idr, n)
          res = res || testFnNameL(test.tArgs, n)
          res = res || (try { environment.get(test.tCont).get._1.contains(n) } catch { case NotFound(_) => false } )
        }
      }
    }
        res
  }
  
  def show(): String = {
    "*** PROCESS ***\n" + components.flatMap(_.show) + "***************\n"
  }
  
  def print() {
    println("*** PROCESS ***")
    for (comp <- components) {
      comp.print()
    }
    println("***************")
  }

}

object Process {

  // Formerly nf2Process
  /** Creates a top level process from an equation system */
  def apply(nf: Closure, args: List[String]): Process = {
    val main = nf.signature.id
    if(main == Closure.voidEquationVariable) {
      new Process()
    } else {
      val eq = nf.environment.get(main).get._2
      val marker = Array.fill(eq.actionCount)(Array.fill(eq.restrictionCount)(false))
      val subArgs = new NameSeq(args.map(component.Free(_)))
      val subRests = freshRestrictions(eq.restrictionCount)
      val (outs, inps, tests, taus, sums) = eqActs(eq, marker, subArgs, subRests, 0, new HashMap(), Nil, Nil, Nil, Nil, Nil)
      val (numComps, compActs, compNames) = components(marker)
      val (fnoL, bnoL, fniL, bniL, idTs, actTs, actSs) = createComps(new Ref(outs), new Ref(inps), new Ref(tests), new Ref(taus), new Ref(sums), numComps, compActs)
      val rL = new Array[Any](numComps).map((_) => new NameSeq())
      eqRests(compNames, numComps, subRests, eq.restrictionCount, rL, 0)
      val compRes = new Array[Component](numComps)
      for(i <- 0 until numComps) { compRes(i) = new Component(rL(i), fnoL(i), bnoL(i), fniL(i), bniL(i), idTs(i), actTs(i), actSs(i)) }
      
      new Process(compRes.toList, nf.environment)
    }
  }
  
  // Formerly instantiateProc
  /** Creates an evolved process by
   *  a) dropping the unevolved component
   *  b) appending the new components.
   */
  def apply(p: Process,
            numComps: Int,
            compNum: Int,
            rL: Array[NameSeq],
            fnoL: Array[TopActionSeq],
            bnoL: Array[TopActionSeq],
            fniL: Array[TopActionSeq],
            bniL: Array[TopActionSeq],
            idTs: Array[TopTestSeq],
            actTs: Array[TopTauSeq],
            actSs: Array[TopSumSeq]): Process = {
    val p1 = p.components.slice(0, compNum)
    val p2 = p.components.slice(compNum + 1, p.countComponents-1)
    val p3 = 
      for(j <- Range(0, numComps).toList) yield
        new Component(rL(j), fnoL(j), bnoL(j), fniL(j), bniL(j), idTs(j), actTs(j), actSs(j))
    
    new Process(p1 ++ p2 ++ p3, p.environment)
  }

  
  /** Creates an evolved process by
   *  a) dropping the two unevolved components
   *  b) appending the new components.
   */
  def apply(p: Process,
            numComps: Int,
            comp1: Int,
            comp2: Int,
            rL: Array[NameSeq],
            fnoL: Array[TopActionSeq],
            bnoL: Array[TopActionSeq],
            fniL: Array[TopActionSeq],
            bniL: Array[TopActionSeq],
            idTs: Array[TopTestSeq],
            actTs: Array[TopTauSeq],
            actSs: Array[TopSumSeq]): Process = {
    val minComp = Math.min(comp1, comp2)
    val maxComp = Math.max(comp1, comp2)
    
    val p1 = p.components.slice(0, minComp)
    val p2 = p.components.slice(minComp+1, maxComp)
    val p3 = p.components.slice(maxComp+1, p.countComponents())
    val p4 = 
      for(j <- Range(0, numComps).toList) yield
        new Component(rL(j), fnoL(j), bnoL(j), fniL(j), bniL(j), idTs(j), actTs(j), actSs(j))
    new Process(p1 ++ p2 ++ p3 ++ p4, p.environment)
  }



  // Auxiliary functions



  def components(a: Array[Array[Boolean]]): (Int, Array[Int], Array[Int]) = {
    
    def getNames(a: Array[Array[Boolean]],
                 acts: Array[Int],
                 numActs: Int,
                 names: Array[Int],
                 numNames: Int,
                 part: Int,
                 i: Int) {
    
	  def getComps(a: Array[Array[Boolean]],
	               acts: Array[Int],
	               numActs: Int,
	               names: Array[Int],
	               numNames: Int,
	               part: Int,
	               j: Int) {
	      for (k <- 0 until numActs) {
	        if (acts(k) == 0 && a(k)(j)) {
	          acts(k) = part
	          getNames(a, acts, numActs, names, numNames, part, k)
	        }
	      }
	    }
	    
	  for (j <- 0 until numNames) {
	    if (names(j) == 0 && a(i)(j)) {
	      names(j) = part
	      getComps(a, acts, numActs, names, numNames, part, j)
	    }
	  }
	}
    
    
    
    val numActs = a.length
    val numNames = a(0).length
    var parts = 1
    val acts = Array.fill(numActs)(0)
    val names = Array.fill(numNames)(0)
    for (i <- 0 until numActs) {
      if (acts(i) == 0) {
        acts(i) = parts
        getNames(a, acts, numActs, names, numNames, parts, i)
        parts += 1
      }
    }
    (parts - 1, acts, names)
  }

  // Auxiliary functions to handle top level process action creation
  def equivalentName(marker: Array[Array[Boolean]],
                 pos: Int,
                 subArgs: NameSeq,
                 subRests: Array[String],
                 parsMarker: HashMap[String, Int]): 
                 Equation.Name => component.Name = {
    case Restricted(i) =>
      marker(pos)(i) = true
      component.Bound(subRests(i))
    case Parameter(i) =>
      try {
        val k = hashtblFind(parsMarker, subArgs(i).s)
        marker(pos)(k) = true
      } catch {
        case NotFound(_) => ()
      }
      subArgs(i)
    case Free(s) => component.Free(s)
    case Internal(i) => component.Input(i)
  }
  
  def equivalentNames(marker: Array[Array[Boolean]],
                 pos: Int,
                 subArgs: NameSeq,
                 subRests: Array[String],
                 parsMarker: HashMap[String, Int])
                 (names: List[Name]): NameSeq = {
    NameSeq(names.map(equivalentName(marker, pos, subArgs, subRests, parsMarker)(_)))
  }
                   
     

  def eqAct(act: Equation.Action,
            marker: Array[Array[Boolean]],
            subArgs: NameSeq,
            subRests: Array[String],
            pos: Int,
            parsMarker: HashMap[String, Int]): TopAction = {
    val (equationType, subject, objects, continuation, arguments) = act
    new TopAction(
      actionType = equationType,
      subject = equivalentName(marker, pos, subArgs, subRests, parsMarker)(subject),
      objects = equivalentNames(marker, pos, subArgs, subRests, parsMarker)(objects),
      continuation = continuation,
      arguments = equivalentNames(marker, pos, subArgs, subRests, parsMarker)(arguments))
  }

  def eqTest(test: Equation.Test,
             marker: Array[Array[Boolean]],
             subArgs: NameSeq,
             subRests: Array[String],
             pos: Int,
             parsMarker: HashMap[String, Int]): TopTest = {
    test match { case (typ, id1, id2, x, a) =>
      new TopTest(
        tst = typ,
        idl = equivalentName(marker, pos, subArgs, subRests, parsMarker)(id1),
        idr = equivalentName(marker, pos, subArgs, subRests, parsMarker)(id2),
        tCont = x,
        tArgs = equivalentNames(marker, pos, subArgs, subRests, parsMarker)(a))
    }
  }

  def eqTau(tau: Tau,
            marker: Array[Array[Boolean]],
            subArgs: NameSeq,
            subRests: Array[String],
            pos: Int,
            parsMarker: HashMap[String, Int]): TopTau = {
    tau match { case (continuation, arguments) =>
      new TopTau(
        tauCont = continuation,
        tauArgs = equivalentNames(marker, pos, subArgs, subRests, parsMarker)(arguments))
    }
  }

  def eqActs(eq: Equation,
                marker: Array[Array[Boolean]],
                subArgs: NameSeq,
                subRests: Array[String],
                startAct: Int,
                parsMarker: HashMap[String, Int],
                startOuts: List[(TopAction, Int)],
                startInps: List[(TopAction, Int)],
                startTests: List[(TopTest, Int)],
                startTaus: List[(TopTau, Int)],
                startSums: List[(TopSum, Int)]):
                  (List[(TopAction, Int)], List[(TopAction, Int)], List[(TopTest, Int)], List[(TopTau, Int)], List[(TopSum, Int)]) = {
    var outs = startOuts
    var accum = startAct
    var inps = startInps
    var tests = startTests
    var taus = startTaus
    var sums = startSums

    for(i <- 0 until eq.numFnOuts) {
      outs = (eqAct(eq.freeOutputs(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::outs
    }
    accum += eq.numFnOuts
    for(i <- 0 until eq.numBnOuts) {
      outs = (eqAct(eq.boundOutputs(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::outs
    }
    accum += eq.numBnOuts
    for(i <- 0 until eq.numFnInps) {
      inps = (eqAct(eq.freeInputs(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::inps
    }
    accum += eq.numFnInps
    for(i <- 0 until eq.numBnInps) {
      inps = (eqAct(eq.boundInputs(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::inps
    }
    accum += eq.numBnInps
    for(i <- 0 until eq.numTests) {
      tests = (eqTest(eq.tests(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::tests
    }
    accum += eq.numTests
    for(i <- 0 until eq.numTaus) {
      taus = (eqTau(eq.taus(i), marker, subArgs, subRests, accum+i, parsMarker), accum+i)::taus
    }
    accum += eq.numTaus
    for(l <- eq.sums) {
      l match { case (sActs, sTests, sTaus) =>
        var sumActs: TopActionSeq = new TopActionSeq()
        var sumTests: TopTestSeq = new TopTestSeq()
        var sumTaus: TopTauSeq = new TopTauSeq()
        for(act <- sActs) {
          sumActs = sumActs.unshift(eqAct(act, marker, subArgs, subRests, accum, parsMarker))
        }
        for(test <- sTests) {
          sumTests = sumTests.unshift(eqTest(test, marker, subArgs, subRests, accum, parsMarker))
        }
        for(tau <- sTaus) {
          sumTaus = sumTaus.unshift(eqTau(tau, marker, subArgs, subRests, accum, parsMarker))
        }
        sums = (TopSum(sumActs, sumTaus, sumTests), accum)::sums
        accum += 1
      }
    }
    (outs, inps, tests, taus, sums)
  }

  // Auxiliary functions to handle top level process component creation
  def createComps[A, B, C](outs: Ref[List[(TopAction, Int)]],
                           inps: Ref[List[(TopAction, Int)]],
                           tests: Ref[List[(TopTest, Int)]],
                           taus: Ref[List[(TopTau, Int)]],
                           sums: Ref[List[(TopSum, Int)]],
                           numComps: Int,
                           compActs: Array[Int]):
    (Array[TopActionSeq], Array[TopActionSeq], Array[TopActionSeq], Array[TopActionSeq], Array[TopTestSeq], Array[TopTauSeq], Array[TopSumSeq]) = {
    val resFnos = Array.fill[TopActionSeq](numComps)(new TopActionSeq())
    val resBnos = Array.fill[TopActionSeq](numComps)(new TopActionSeq())
    val resFnis = Array.fill[TopActionSeq](numComps)(new TopActionSeq())
    val resBnis = Array.fill[TopActionSeq](numComps)(new TopActionSeq())
    val resTests = Array.fill[TopTestSeq](numComps)(new TopTestSeq())
    val resTaus = Array.fill[TopTauSeq](numComps)(new TopTauSeq())
    val resSums = Array.fill[TopSumSeq](numComps)(new TopSumSeq())
    val numOuts = (!outs).length
    val numInps = (!inps).length
    val numTests = (!tests).length
    val numTaus = (!taus).length
    for(i <- 0 until compActs.length) {
      if(i < (numOuts + numInps)) {
        val (act, actPos, out) =
          if(i < numOuts) {
            val (res, actPos) = (!outs).head
            outs := (!outs).tail
            (res, actPos, true)
          } else {
            val (res, actPos) = (!inps).head
            inps := (!inps).tail
            (res, actPos, false)
          }
        val fn = act.subject match {
          case component.Bound(_) => false
          case _ => true
        }
        if(fn) {
          if(out) {
            resFnos(compActs(actPos) - 1) = resFnos(compActs(actPos) - 1).unshift(act)
          } else {
            resFnis(compActs(actPos) - 1) = resFnis(compActs(actPos) - 1).unshift(act)
          }
        } else {
          if(out) {
            resBnos(compActs(actPos) - 1) = resBnos(compActs(actPos) - 1).unshift(act)
          } else {
            resBnis(compActs(actPos) - 1) = resBnis(compActs(actPos) - 1).unshift(act)
          }
        }
      } else if(i < numOuts + numInps + numTests) {
        val (test, testPos) = (!tests).head
        tests := (!tests).tail
        resTests(compActs(testPos) - 1) = resTests(compActs(testPos) - 1).unshift(test)
      } else if(i < numOuts + numInps + numTests + numTaus) {
        val (tau, tauPos) = (!taus).head
        taus := (!taus).tail
        resTaus(compActs(tauPos) - 1) = resTaus(compActs(tauPos) - 1).unshift(tau)
      } else {
        val (sum, sumPos) = (!sums).head
        sums := (!sums).tail
        resSums(compActs(sumPos) - 1) = resSums(compActs(sumPos) - 1).unshift(sum)
      }
    }
    (resFnos, resBnos, resFnis, resBnis, resTests, resTaus, resSums)
  }

  def eqRests[A](compNames: Array[Int],
                 numComps: A,
                 subRests: Array[String],
                 size: Int,
                 resNames: Array[NameSeq],
                 startPos: Int) {
    for(i <- 0 until size) {
      if(compNames(i + startPos) != 0) {
        resNames(compNames(i + startPos) - 1) = resNames(compNames(i + startPos) - 1).unshift(component.Bound(subRests(i)))
      }
    }
  }

  // Auxiliary functions to testFn

  def testFnName(n: component.Name, arg: String): Boolean = {
    n match {
      case component.Free(s) => s == arg
      case _ => false
    }
  }

  def testFnNameL(l: NameSeq, arg: String): Boolean = {
    l.foldLeft(false)((b, n) => b || testFnName(n, arg))
  }

  def testFnAux(act: TopAction, n: String, fnSub: Boolean): Boolean = {
    (fnSub && testFnName(act.subject, n)) || (act.actionType == Output && testFnNameL(act.objects, n)) || testFnNameL(act.arguments, n)
  }

  // Tests if a process has a determined free name
  def testFn(p: Process, n: String): Boolean = {
    var res = false
    
    for(comp <- p.components if !res) {
      for(fnOut <- comp.freeOutputs if !res) {
        res = testFnAux(fnOut, n, true)
        res = res || (try { p.environment.get(fnOut.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(fnInp <- comp.freeInputs if !res) {
        res = testFnAux(fnInp, n, true)
        res = res || (try { p.environment.get(fnInp.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(bnOut <- comp.boundOutputs if !res) {
        res = testFnAux(bnOut, n, true)
        res = res || (try { p.environment.get(bnOut.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(bnInp <- comp.boundInputs if !res) {
        res = testFnAux(bnInp, n, true)
        res = res || (try { p.environment.get(bnInp.continuation).get._1.contains(n) } catch { case NotFound(_) => false})
      }
      for(test <- comp.idTests if !res) {
        res = testFnName(test.idl, n)
        res = res || testFnName(test.idr, n)
        res = res || testFnNameL(test.tArgs, n)
        res = res || (try { p.environment.get(test.tCont).get._1.contains(n) } catch { case NotFound(_) => false })
      }
      for(tau <- comp.actTaus if !res) {
        res = testFnNameL(tau.tauArgs, n)
        res = res || (try { p.environment.get(tau.tauCont).get._1.contains(n) } catch { case NotFound(_) => false })
      }
      for(TopSum(acts, taus, tests) <- comp.actSums if !res){
        for(act <- acts if !res) {
          res = res || testFnAux(act, n, true)
          res = res || (try { p.environment.get(act.continuation).get._1.contains(n) } catch { case NotFound(_) => false })
        }
        for(tau <- taus if !res) {
          res = res || testFnNameL(tau.tauArgs, n)
          res = res || (try { p.environment.get(tau.tauCont).get._1.contains(n) } catch { case NotFound(_) => false } )
        }
        for(test <- tests if !res) {
          res = testFnName(test.idl, n)
          res = res || testFnName(test.idr, n)
          res = res || testFnNameL(test.tArgs, n)
          res = res || (try { p.environment.get(test.tCont).get._1.contains(n) } catch { case NotFound(_) => false } )
        }
      }
    }
        res
  }

  // Auxiliary functions to freeNames

  def freeName(n: component.Name, h: HashMap[String, Int], res: Ref[List[String]]) {
    n match {
      case component.Free(s) =>
        if(!h.contains(s)) {
          res := s::(!res)
        }
      case _ => ;
    }
  }

  def freeNameL(l: NameSeq, h: HashMap[String, Int], res: Ref[List[String]]) {
    for(n <- l) { freeName(n, h, res) }
  }

  def fnEqsAux[A](l: List[A], h: HashMap[A, Int], res: Ref[List[A]]) {
    for(a <- l) {
      if(!h.contains(a)) {
        h.put(a, 0)
        res := a::(!res)
      }
    }
  }




  // Action update handling
  def procName(oldn: String,
               newn: String,
               marker: Array[Array[Boolean]],
               rmarker: HashMap[String, Int],
               pos: Int): 
               component.Name => component.Name = {
    case component.Bound(s) =>
      if(s.equals(oldn)) {
        component.Free(newn)
      } else {
        marker(pos)(hashtblFind(rmarker, s)) = true
        component.Bound(s)
      }
    case default => default
  }

  def procNames(oldn: String,
                newn: String,
                marker: Array[Array[Boolean]],
                rmarker: HashMap[String, Int],
                pos: Int): NameSeq => NameSeq =
    NameSeq.fmap(Monoid.extend(procName(oldn, newn, marker, rmarker, pos)))
                  
  def procAct(oldn: String,
              newn: String,
              marker: Array[Array[Boolean]],
              rmarker: HashMap[String, Int],
              pos: Int,
              fnsub: Boolean)(act: TopAction): TopAction = {
    new TopAction(
      actionType = act.actionType,
      subject = if(fnsub) { act.subject } else { procName(oldn, newn, marker, rmarker, pos)(act.subject) },
      objects = if(act.actionType == Output) { procNames(oldn, newn, marker, rmarker, pos)(act.objects) } else { act.objects },
      continuation = act.continuation,
      arguments = procNames(oldn, newn, marker, rmarker, pos)(act.arguments) )
  }

  def procTest(oldn: String,
               newn: String,
               marker: Array[Array[Boolean]],
               rmarker: HashMap[String, Int],
               pos: Int)(test: TopTest): TopTest = {
    new TopTest(
      tst = test.tst,
      idl = procName(oldn, newn, marker, rmarker, pos)(test.idl),
      idr = procName(oldn, newn, marker, rmarker, pos)(test.idr),
      tCont = test.tCont,
      tArgs = procNames(oldn, newn, marker, rmarker, pos)(test.tArgs))
  }

  def procTau(oldn: String,
              newn: String,
              marker: Array[Array[Boolean]],
              rmarker: HashMap[String, Int],
              pos: Int)(tau: TopTau): TopTau = {
    new TopTau(
      tauCont = tau.tauCont,
      tauArgs = procNames(oldn, newn, marker, rmarker, pos)(tau.tauArgs))
  }

  def procActs[A](comp: Component,
                  marker: Array[Array[Boolean]],
                  oldn: String,
                  revn: String,
                  startAct: Int,
                  rmarker: HashMap[String, Int],
                  startOuts: List[(TopAction, Int)],
                  startInps: List[(TopAction, Int)],
                  startTests: List[(TopTest, Int)],
                  startTaus: List[(TopTau, Int)],
                  startSums: List[(TopSum, Int)],
                  inpInd: Int,
                  outInd: Int,
                  fn: Boolean,
                  ti: Int,
                  taui: Int):
                    (Ref[List[(TopAction, Int)]],
                      Ref[List[(TopAction, Int)]],
                      Ref[List[(TopTest, Int)]],
                      Ref[List[(TopTau, Int)]],
                      Ref[List[(TopSum, Int)]]) = {
    var outs = startOuts
    var inps = startInps
    var tests = startTests
    var taus = startTaus
    var sums = startSums
    var inpSumI = if(fn) { comp.nfreeInputs } else { comp.nboundInputs }
    var outSumI = if(fn) { comp.nfreeOutputs } else { comp.nboundOutputs }
    var testSumI = comp.ntests
    var tauSumI = comp.ntaus
    var accum = startAct
    def decrAccum() { accum = accum - 1}

    for((v,i) <- comp.freeOutputs.zipWithIndex) {
      if(!fn || outInd != i) {
        val pos = accum + i
        outs = (procAct(oldn, revn, marker, rmarker, pos, true)(v), pos)::outs
      } else {
        decrAccum()
      }
    }
    accum = accum + comp.nfreeOutputs
    for((v,i) <- comp.boundOutputs.zipWithIndex) {
      if(fn || outInd != i) {
        outs = (procAct(oldn, revn, marker, rmarker, accum+i, false)(v), accum+i)::outs
      } else {
        accum = accum -1
      }
    }
    accum = accum + comp.nboundOutputs
    for((v,i) <- comp.freeInputs.zipWithIndex) {
      if(!fn || inpInd != i) {
        inps = (procAct(oldn, revn, marker, rmarker, accum+i, true)(v), accum+i)::inps
      } else {
        decrAccum()
      }
    }
    accum = accum + comp.nfreeInputs
    for((v,i) <- comp.boundInputs.zipWithIndex) {
      if(fn || inpInd != i) {
        inps = (procAct(oldn, revn, marker, rmarker, accum+i, false)(v), accum+i)::inps
      } else {
        decrAccum()
      }
    }
    accum = accum + comp.nboundInputs
    for((v,i) <- comp.idTests.zipWithIndex) {
      if(i != ti) {
        tests = (procTest(oldn, revn, marker, rmarker, accum + i)(v), accum+i)::tests
      } else {
        decrAccum()
      }
    }
    accum = accum + comp.ntests
    for((v,i) <- comp.actTaus.zipWithIndex) {
      if(i != taui) {
        taus = (procTau(oldn, revn, marker, rmarker, accum + i)(v), accum + i)::taus
      } else {
        decrAccum()
      }
    }
    accum = accum + comp.ntaus
    for(TopSum(acts, taus, tests) <- comp.actSums) {
      if(!(((inpInd >= inpSumI) && (inpInd < inpSumI + acts.length))
        || ((outInd >= outSumI) && (outInd < outSumI + acts.length))
        || ((taui >= tauSumI) && (taui < tauSumI + taus.length))
        || ((ti >= testSumI) && (ti < testSumI + tests.length)))) {
        val newActs = acts.reverseMap(procAct(oldn, revn, marker, rmarker, accum, false)).asInstanceOf
        val newTaus = taus.reverseMap(procTau(oldn, revn, marker, rmarker, accum)).asInstanceOf
        val newTests = tests.reverseMap(procTest(oldn, revn, marker, rmarker, accum)).asInstanceOf
        sums = (TopSum(newActs, newTaus, newTests), accum /* +1 */)::sums
      }
      inpSumI = inpSumI + acts.length
      outSumI = outSumI + acts.length
      tauSumI = outSumI + taus.length
      testSumI = testSumI + tests.length
    }
    (new Ref(outs), new Ref(inps), new Ref(tests), new Ref(taus), new Ref(sums))
  }

  // Restring name update handling
  def procRests[A](compNames: Array[Int],
                   numComps: A,
                   comp: Component,
                   pos: Int,
                   resNames: Array[NameSeq],
                   startPos: Int) {
    for(i <- 0 until comp.countRestrictions) {
      val newRestPos = if(i < pos) { i } else if(i < comp.countRestrictions - 1) { i+1 } else { -1 }
      if(newRestPos != -1 && compNames(i+startPos) != 0) {
        resNames(compNames(i+startPos) - 1) =
          resNames(compNames(i+startPos) - 1).unshift(component.Bound(comp.restrictions(newRestPos).s))
      }
    }
  }

  // Returns a process where a restricted name revelation has taken place
  def revealComponents(compNum: Int,
                       restNum: Int,
                       revn: String)(p: Process): Process = {
    println("rev_components(_, " + compNum + ", " + restNum + ", " + revn + ")")
    val comp = p.components(compNum)
    val oldn = comp.restrictions(restNum).s
    val marker = Array.fill[Array[Boolean]](p.components(compNum).countActs())(Array.fill[Boolean](comp.countRestrictions-1)(false))
    val rmarker = comp.restrictionMarkers(0, restNum)
    val (outs, inps, tests, taus, sums) = procActs(comp, marker, oldn, revn, 0, rmarker, Nil, Nil, Nil, Nil, Nil, -1 , -1 , true, -1, -1)
    val (numComps, compActs, compNames) = components(marker)
    val (fnoL, bnoL, fniL, bniL, idTs, actTs, actSs) = createComps(outs, inps, tests, taus, sums, numComps, compActs)
    val rL = Array.fill[NameSeq](numComps)(new NameSeq())
    procRests(compNames, numComps, comp, restNum, rL, 0)
    Process(p, numComps, compNum, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, actSs)
  }

  // Auxiliary functions to findLabel

  def matchName(s: String, n: component.Name): Boolean = {
    n match {
      case component.Free(x) => x == s
      case _ => false
    }
  }

  def matchList(sl: List[String], nl: NameSeq, marker: Array[Boolean], i: Int, h: HashMap[String, String]): (Boolean, List[(String, String)]) = {
    val default = (false, Nil)
    def matchList: List[component.Name] => (Boolean, List[(String, String)]) = {
      case Nil =>
        sl match {
          case Nil => (true, Nil)
          case _ => default
        }
      case component.Bound(n)::nltl =>
        if(marker(i)) {
          sl match {
            case Nil => default
            case s::sltl =>
              val (res, resL) = matchList(nltl)
              if(res) {
                if(!h.contains(n)) {
                  val ns = if(s.equals("_")) { freshAlias() } else { s }
                  h.put(n, ns)
                  (true, (ns, n)::resL)
                } else {
                  if(hashtblFind(h, n).equals(s)) {
                    (true, resL)
                  } else {
                    default
                  }
                }
              } else {
                default
              }
          }
        } else {
          default
        }
      case component.Free(n)::nltl =>
        sl match {
          case Nil => default
          case s::sltl =>
            val (res, resL) = matchList(nltl)
            if(res) {
              (s.equals(n) || s.equals("_"), resL)
            } else {
              default
            }
        }
      case component.Input(i)::_ => default 
    }
    matchList(nl.toList)
  }

  def matchLab(lab: ml.Label, act: TopAction, marker: Array[Boolean]): (Boolean, List[(String, String)]) = {
  	(lab, act.actionType) match {
  	  case (ml.Input(channel, arguments), Input) =>
  	    (arguments.length == act.objects.length && matchName(channel, act.subject), Nil)
  	  case (ml.Output(channel, arguments), Output) =>
  	    if(arguments.length == act.objects.length && matchName(channel, act.subject)) {
          matchList(arguments, act.objects, marker, 0, new HashMap())
        } else {
          (false, Nil)
        }
  	  case noMatch =>
  	    (false, Nil)
  	}
  }

  // Finds an action given the label and a starting point
  def findLabel(p: Process,
                lab: ml.Label,
                comp: Int,
                ind: Int,
                marker: Array[Boolean]): (Boolean, Int, Int, List[(String, String)]) = {
    var notFound = true
    var reveals: List[(String, String)] = Nil
    var curComp = comp
    var curInd = ind
    val size1 = p.countComponents()
    while(curComp < size1 && notFound) {
      val (size2, acts) =
        lab match {
          case ml.Input(channel, arguments) =>
            (p.components(curComp).nfreeInputs, p.components(curComp).freeInputs)
          case ml.Output(channel, arguments) =>
            (p.components(curComp).nfreeOutputs, p.components(curComp).freeOutputs)
      	}
      while(curInd < size2 && notFound) {
        val (res, resL) = matchLab(lab, acts(curInd), marker)
        if(res) {
          notFound = false
          reveals = resL
        } else {
          curInd = curInd + 1
        }
      }
      if(notFound) {
        var sumInd = curInd - size2
        for(TopSum(acts,_,_) <- p.components(curComp).actSums if notFound) {
          for(act <- acts if notFound) {
            if(sumInd == 0) {
              val (res, resL) = matchLab(lab, act, marker)
              if(res) {
                notFound = false
                reveals = resL
              } else {
                curInd = curInd + 1
              }
            } else {
              sumInd = sumInd - 1
            }
          }
        }
      }
      if(notFound) {
        curComp = curComp + 1
        curInd = 0
      }
    }
    (notFound, curComp, curInd, reveals)
  }

  // Finds a restricted name component
  def findRest(p: Process, comp: Int, n: String): Int = {
    for(i <- 0 until p.components(comp).countRestrictions) {
      if(p.components(comp).restrictions(i).s.equals(n)) {
        return i
      }
    }
    -1
  }

  // Finds a component that holds restrictions
  def findRestrictedComponent(p: Process, i: Int): Int = {
    for((comp, i) <- p.components.zipWithIndex.drop(i)) {
      if(comp.countRestrictions > 0) {
        return i
      }
    }
    -1
  }

  def getPosSum[A](seq: Seq[A], ind: Int, i: Int): A = {
    def getPosSum: (List[A], Int) => A = {
      case (Nil, _) => throw Fail()
      case (hd::tl, i) => if(ind == i) { hd } else { getPosSum(tl, i+1) }
    }
    getPosSum(seq.toList, i)
  }

  def getActSums(sums: TopSumSeq, ind: Int, i: Int): TopAction = {
    def getActSums: (List[TopSum], Int) => TopAction = {
      case (Nil, _) => throw new Error
      case (TopSum(acts, taus, tests)::tl, i) =>
        if(ind < acts.length + i) {
          getPosSum(acts, ind, i)
        } else {
          getActSums(tl, i + acts.length)
        }
    }
    getActSums(sums.toList, i)
  }

  // Auxiliary functions to findFnTau and findBnTau

  def matchTauName(n1: component.Name, n2: component.Name): Boolean = {
    (n1, n2) match {
      case (component.Bound(x), component.Bound(y)) => x == y
      case (component.Free(x), component.Free(y)) => x == y
      case _ => false
    }
  }

  def matchTau(inp: TopAction, out: TopAction): Boolean = {
    (inp.actionType == Input && 
     out.actionType == Output && 
     matchTauName(inp.subject, out.subject) && 
     inp.objects.length == out.objects.length)
  }


  // This is the original translation.  Use it for testing.
  def findFnTauOriginal(p: Process, inpc: Int, inpi: Int, outc: Int, outi: Int): (Boolean, Int, Int, Int, Int) = {
    // FIXME: ugh, this is a disgusting function, and it's probably broken.  See findFnTau for my working proposal.
    var notFound = true // notFound can be factored out completely by using return statements
    var inpComp = inpc // inpComp, inpInd, outComp, and outInd track the components and their subacts
    var inpInd = inpi  // These values are returned at the end of the method.
    var outComp = outc
    var outInd = outi
    while(inpComp < p.countComponents() && notFound) { // Begin outer loop over all components
      while(inpInd < p.components(inpComp).nfreeInputs && notFound) { // Iterate over nfInps
        while(outComp < p.countComponents() && notFound) { // Begin inner loop over all components
          // LoopA Invariant Negated = (outInd == p.components(outComp).nfreeOutputs || !notFound)
          while(outInd < p.components(outComp).nfreeOutputs && notFound) { // Iterate over nfOuts
            if(matchTau(p.components(inpComp).freeInputs(inpInd), p.components(outComp).freeOutputs(outInd))) {
              notFound = false
            } else {
              outInd = outInd + 1 // Always happens, unless a match is found.
            }
          }
          if(notFound) {
            // Note: outSumInd = 0 follows from the negated invariant of loopA and the predicate immediately prior to this note
            // Furthermore, because outSumInd doesn't vary once it is zero, it remains 0 through the entire control flow.
            // Therefore, the test is a no-op, and outSumInd can be erased from the function.
            var outSumInd = outInd - p.components(outComp).nfreeOutputs
            try {
              for(TopSum(acts, taus, tests) <- p.components(outComp).actSums if notFound) {
                for(out <- acts if notFound) {
                  if(outSumInd == 0) { // Always true
                    if(out.isFnAct() && out.actionType == Output) { // Checks that we're examining the right type of act
                      if(matchTau(p.components(inpComp).freeInputs(inpInd), out)) {
                        notFound = false // Could've been a return statement...
                      } else {
                        outInd = outInd + 1 // Always happens, unless a match is found.
                      }
                    }
                  } else {
                    outSumInd = outSumInd - 1 // Never happens
                  }
                }
              }
            } catch { case Found => ; }
          }
          if(notFound) { // Update the while loop indices
            outComp = outComp + 1
            outInd = 0
          }
        }
        if(notFound) { // Update the while loop indices
          inpInd = inpInd + 1
          outComp = 0
          outInd = 0
        }
      }
      if(notFound) { // Start checking the input actions of the sum component.
      var inpSumInd = inpInd - p.components(inpComp).nfreeInputs
        var inpSumPos = 0
        try {
          for(TopSum(acts, taus, tests) <- p.components(inpComp).actSums if notFound) {
            for(inp <- acts) {
              if(inpSumInd == 0) {
                if(inp.isFnAct && inp.actionType == Internal) {
                  while(outComp < p.countComponents() && notFound) {
                    while(outInd < p.components(outComp).nfreeOutputs && notFound) {
                      if(matchTau(inp, p.components(outComp).freeOutputs(outInd))) {
                        notFound = false
                        throw Found
                      } else {
                        outInd = outInd + 1
                      }
                    }
                    if(notFound) {
                      // Note: the same logic follows here as above.  Therefore, you should ignore outSumInd
                      var outSumInd = outInd - p.components(outComp).nfreeOutputs
                      var outSumPos = 0
                      for(TopSum(acts, taus, tests) <- p.components(outComp).actSums) {
                        if(inpComp != outComp || inpSumPos != outSumPos) { // Check you're not matching in the same sum
                          for(out <- acts) {
                            if(outSumInd == 0) { // Always true
                              if(out.isFnAct && out.actionType == Output) { // Checks for the right type
                                if(matchTau(inp, out)) { // Check for a match
                                  notFound = false
                                } else {
                                  outInd = outInd + 1 // Increment the index if no match
                                }
                              } else {
                                outInd = outInd + 1 // Increment the index if the wrong type
                              }
                            } else {
                              outSumInd = outSumInd - 1 // Never happens
                            }
                          }
                        } else { // If you are matching the same sum, then you need to do something special...
                        // Okay, here's some craziness.
                        val outSumLen = acts.length // Simple alias, okay
                          if(outSumInd >= outSumLen) { // Only true if acts.length == 0
                            outSumInd = outSumInd - outSumLen // Thus 0 = 0.  This is a no-op
                          } else { // acts.length != 0
                            outSumInd = 0 // 0 = 0. This is a no-op
                            outInd = outInd + outSumLen
                            // This last statement simulates skipping all of the acts in this sum.
                          }
                        }
                        outSumPos = outSumPos + 1
                      }
                    }
                    if(notFound) {
                      outComp = outComp + 1
                      outInd = 0
                    }
                  }
                  inpInd = inpInd + 1
                  outComp = 0
                  outInd = 0
                } else {
                  inpSumInd = inpSumInd - 1
                }
              }
            }
            inpSumPos = inpSumPos + 1
          }
        } catch { case Found => ; }
        if(notFound) {
          inpComp = inpComp + 1
          inpInd = 0
          outComp = 0
          outInd = 0
        }
      }
    }
    (notFound, inpComp, inpInd, outComp, outInd)
  }

  // Finds a synchronization in a free name
  def findFnTau(p: Process, inpc: Int, inpi: Int, outc: Int, outi: Int): (Boolean, Int, Int, Int, Int) = {
    // Outer loop
    for((inpC, inpCi) <- p.components.zipWithIndex.slice(inpc, p.components.length)) {
      var inpA = p.getTau(true, Input, inpCi, 0)
      var inpAi = 0
      while(inpA != None) {

        // Identical inner loop
        for((outC, outCi) <- p.components.zipWithIndex.slice(outc, p.components.length)) {
          var outA = p.getTau(true, Output, outCi, 0)
          var outAi = 0
          while(outA != None) {
            
            // Predicate
            // Note: The Either type in the following match denotes:
            // Left: The act was returned from freeInputs
            // Right; The act was returned in a tuple with it's containing sum
            (inpA.get, outA.get) match {

              // Neither of the acts are in a sum.
              case (Left(inp),Left(out)) =>
                if(matchTau(inp,out)) { return (false, inpCi, inpAi, outCi, outAi) }

              // Only one act is in a sum.
              case (Left(inp), Right((out,_))) =>
                if(out.actionType == Output && out.isFnAct())
                  if(matchTau(inp,out)) { return (false, inpCi, inpAi, outCi, outAi) }

              // Only one act is in a sum.
              case (Right((inp,_)), Left(out)) =>
                if(inp.actionType == Internal && inp.isFnAct())
                  if(matchTau(inp,out)) { return (false, inpCi, inpAi, outCi, outAi) }

              //Both acts are in a sum.
              case (Right((inp,inSum)), Right((out, outSum))) =>
                if(inSum != outSum) {
                  if(inp.actionType == Internal && inp.isFnAct())
                    if(out.actionType == Output && out.isFnAct())
                      if(matchTau(inp,out)) { return (false, inpCi, inpAi, outCi, outAi) }
                }
            }

            // Increment the inner loop counter.
            outA = p.getTau(true, Output, outCi, outAi+1)
            outAi = outAi+1
          }
        }

        // Increment the outer loop counter.
        inpA = p.getTau(true, Input, inpCi, inpAi+1)
        inpAi = inpAi+1
      }
    }

    // Not found.
    (true, 0, 0, 0, 0)
  }


    // Finds a synchronization in a bound name
    def findBnTau(p: Process, startC: Int, inpi: Int, outi: Int): (Boolean, Int, Int, Int) = {

      // Outer loop
      for((c, ci) <- p.components.zipWithIndex.slice(startC, p.components.length)) {
        var inpA = p.getTau(true, Input, ci, 0)
        var inpAi = 0
        while(inpA != None) {

          // Modified inner loop, uses the same component
          var outA = p.getTau(true, Output, ci, 0)
          var outAi = 0
          while(outA != None) {

            // Predicate
            // Note: The Either type in the following match denotes,
            // Left: The act was returned from freeInputs
            // Right; The act was returned in a tuple with it's containing sum
            (inpA.get, outA.get) match {

              // Neither of the acts are in a sum.
              case (Left(inp),Left(out)) =>
                if(matchTau(inp,out)) { return (false, ci, inpAi, outAi) }

              // Only one act is in a sum.
              case (Left(inp), Right((out,_))) =>
                if(out.actionType == Output && out.isFnAct())
                  if(matchTau(inp,out)) { return (false, ci, inpAi, outAi) }

              // Only one act is in a sum.
              case (Right((inp,_)), Left(out)) =>
                if(inp.actionType == Internal && inp.isFnAct())
                  if(matchTau(inp,out)) { return (false, ci, inpAi, outAi) }

              //Both acts are in a sum.
              case (Right((inp,inSum)), Right((out, outSum))) =>
                if(inSum != outSum) {
                  if(inp.actionType == Internal && inp.isFnAct())
                    if(out.actionType == Output && out.isFnAct())
                      if(matchTau(inp,out)) { return (false, ci, inpAi, outAi) }
                }
            }

            // Increment the inner loop counter.
            outA = p.getTau(true, Output, ci, outAi+1)
            outAi = outAi+1
          }

          // Increment the outer loop counter.
          inpA = p.getTau(true, Input, ci, inpAi+1)
          inpAi = inpAi+1
        }
      }
      (true, 0, 0, 0)
    }

  // Auxiliary function to findTest
  def matchId(test: TopTest): Boolean = {
    (test.idl, test.idr) match {
      case (component.Free(s1), component.Free(s2)) =>
        if(test.tst == pc.Equals) { s1.equals(s2) } else { !s1.equals(s2) }
      case (component.Bound(s1), component.Bound(s2)) =>
        if(test.tst == pc.Equals) { s1.equals(s2) } else { !s1.equals(s2) }
      case _ => false
    }
  }

  // Finds a test prefix ready to fire
  def findTest(p: Process, comp: Int, ind: Int): (Boolean, Int, Int) = {
    for((comp, compI) <- p.components.zipWithIndex.slice(comp, p.components.length)) {
      for((test, testI) <- comp.idTests.zipWithIndex) {
        if(matchId(test)) {
          return (true, compI, testI)
        }
      }
      for(TopSum(_,_,tests) <- comp.actSums) {
        for((test, testI) <- tests.zipWithIndex) {
          if(matchId(test)) {
            return (true, compI, comp.ntests + testI)
          }
        }
      }
    }
    (false, 0, 0)
  }


  // Finds a tau prefix
  def findTauPref(p: Process, comp: Int, ind: Int): (Boolean, Int, Int) = {
    var tauInd = ind
    for((comp, compI) <- p.components.zipWithIndex.slice(comp, p.countComponents())) {
      if(tauInd < comp.ntaus) {
        return (true, compI, tauInd)
      }
      var sumInd = tauInd - comp.ntaus
      for(TopSum(_,taus,_) <- comp.actSums) {
        for(tau <- taus) {
          if(sumInd == 0) {
            return (true, compI, tauInd)
          } else {
            sumInd = sumInd - 1
          }
        }
      }
    }
    (false, 0, 0)
  }

  // Auxiliary function to reactTauPref
  def getTauSums(sums: TopSumSeq, ind: Int, i: Int): TopTau = {
    def getTauSums: (List[TopSum], Int) => TopTau = {
      case (Nil, _) => throw component.Error
      case (TopSum(_,taus,_)::tl, i) =>
        if(ind < taus.length + i) {
          getPosSum(taus, ind, i)
        } else {
          getTauSums(tl, i + taus.length)
        }
    }
    getTauSums(sums.toList, i)
  }

  // Handles bound name output revelation
  def findNewPos(p: Process, oldNcomps: Int, oldInd: Int): (Int, Int) = {
    var resInd = oldInd
    for((comp, compI) <- p.components.zipWithIndex.slice(oldNcomps, p.components.length)) {
      if(resInd < comp.nfreeOutputs) {
        return (compI, resInd)
      }
      var indAux = resInd
      for(TopSum(acts,_,_) <- comp.actSums) {
        if(indAux < acts.length) {
          return (compI, resInd)
        } else {
          indAux = indAux - acts.length
        }
      }
      resInd = indAux - comp.nfreeOutputs
    }
    (oldNcomps, resInd)
  }

  // Auxiliary function to findName and findAction
  def testAll(l: NameSeq, h: HashMap[String, Boolean]): (Boolean, List[(String, String)]) = {
    def testAll: List[component.Name] => (Boolean, List[(String, String)]) = {
      case Nil => (true, Nil)
      case component.Input(_)::_ => (false, Nil)
      case component.Free(_)::tl => testAll(tl)
      case component.Bound(x)::tl =>
        val (res, resL) = testAll(tl)
        if(res) {
          if(!h.contains(x)) {
            h.put(x, true)
            (true, (freshAlias(), x)::resL)
          } else {
            (true, resL)
          }
        } else {
          (false, Nil)
        }
      
    }
    testAll(l.toList)
  }

  // Finds an action given the subject name
  def findName(p: Process, name: String, actT: IO, nameC: Int, nameI: Int): (Boolean, Int, Int, List[(String, String)]) = {
    var reveals = Nil
    for((comp, nameComp) <- p.components.zipWithIndex.slice(nameC, p.countComponents())) {
      val acts = if(actT == Internal) { comp.freeInputs } else { comp.freeOutputs }
      for((act, nameInd) <- acts.zipWithIndex.slice(nameI, acts.length)) {
        if(act.subject.s.equals(name)) {
          if(actT == Output) {
            val (res, resL) = testAll(act.objects, new HashMap())
            if(res) {
              return (true, nameComp, nameInd, resL)
            }
          } else {
            return (true, nameComp, nameInd, reveals)
          }
        }
      }

      for(TopSum(sumActs, _, _) <- comp.actSums) {
        for((act, i) <- sumActs.zipWithIndex) {
          if(actT == act.actionType && act.isFnAct() && name.equals(act.subject.s)) {
            if(actT == Output) {
              val (res, resL) = testAll(act.objects, new HashMap())
              if(res) {
                return (true, nameComp, acts.length + i, resL)
              }
            } else {
              return (true, nameComp, acts.length + i, reveals)
            }
          }
        }
      }
    }
    (false, 0, 0, Nil)
  }

  // Finds an action given the action type
  def findAction(p: Process, actT: IO, startComponent: Int, ind: Int): (Boolean, Int, Int, List[(String, String)]) = {
    var reveals = Nil
    for((comp, nameComp) <- p.components.zipWithIndex.slice(startComponent, p.countComponents())) {
      val acts = if(actT == Internal) { comp.freeInputs } else { comp.freeOutputs }
      for((act, nameInd) <- acts.zipWithIndex.slice(ind, acts.length)) {
        if(actT == Output) {
          val (res, resL) = testAll(act.objects, new HashMap())
          if(res) {
            return (true, nameComp, nameInd, resL)
          }
        } else {
          return (true, nameComp, nameInd, reveals)
        }
      }

      for(TopSum(sumActs, _, _) <- comp.actSums) {
        for((act, i) <- sumActs.zipWithIndex) {
          if(actT == act.actionType && act.isFnAct()) {
            if(actT == Output) {
              val (res, resL) = testAll(act.objects, new HashMap())
              if(res) {
                return (true, nameComp, acts.length + i, resL)
              }
            } else {
              return (true, nameComp, acts.length + i, reveals)
            }
          }
        }
      }
    }
    (false, p.countComponents(), if(actT == Input) { p.components(p.countComponents()-1).nfreeInputs } else { p.components(p.countComponents()-1).nfreeOutputs }, Nil)
  }

  /*
  // Auxiliary function to nextReactAux
  def nameToString(l: List[Name]): List[String] = {
    l.map(_.s)
  }
  */


  // Auxiliary function to congruentN
  def cutSuppressed[A](l: List[A], suppressed: List[A], fix: List[A]): List[A] = {
    l.filter((x) => !suppressed.contains(x) && !fix.contains(x))
  }

  /*
  // Handle sum comparison
  def sums2Ks(acts: List[TopAction], taus: List[TopTau], tests: List[TopTest]): List[ActKind] = {
    acts.map(ActK) ++ taus.map(TauK) ++ tests.map(TestK)
  }
  
  def selectSumJ[A](nacts: Int, ntaus: Int, ntests: A, i: Int): Int = {
    if(i < nacts) {
      0
    } else if(i - nacts < ntaus) {
      nacts
    } else {
      ntaus
    }
  }

  def topSumJ(nacts: Int, ntaus: Int, ntests: Int, i: Int): Int = {
    if(i < nacts) {
      nacts
    } else if(i - nacts < ntaus) {
      nacts + ntaus
    } else {
      nacts + ntaus + ntests
    }
  }


  private def selectJ(c: Component, i: Int): Int = {
    val all = List(c.nfreeOutputs(), c.nboundOutputs(), c.nfreeInputs(), c.nboundInputs(), c.ntests(), c.ntaus)
    all.foldLeft(0)((acc, x) => if(i < acc + x) { acc } else { acc + x })
  }

  private def topJ(c: Component, i: Int): Int = {
    val all = List(c.nboundOutputs(), c.nfreeInputs(), c.nboundInputs(), c.ntests(), c.ntaus)
    all.foldLeft(c.nfreeOutputs())((acc, x) => if(i < acc) { acc } else { acc + x })
  }
  */
  
  // Auxiliar functions and variables to congruentN
  def singles[A](l: List[A], l2: List[(List[A], List[A])]): List[(List[A], List[A])] = {
    l.map(x => (List(x),List(x))) ++ l2
  }

  val globalSuppression: Ref[List[String]] = new Ref(List[String]())

//      val globFix: List[A] = new Ref(MutableList[A]())            tf is this?

  def matchArgs[A, B](args1: List[A], args2: List[B], el: (List[A], List[B])): List[(List[A], List[B])] = {
    args1.map(List(_)).zip(args2.map(List(_)))++List(el)
  }

  // Determines if two processes are equivalent
  def congruentN(val1: (Process, List[String]), val2: (Process, List[String])): Boolean = {
    val (p1, p1Args) = val1
    val (p2, p2Args) = val2
    val supp = !globalSuppression
    if(p1.countComponents() != p2.countComponents()) {
      false
    } else {
      val (fnP1, fnP2) = (p1.freeNames(), p2.freeNames())
      val(fnP1Supp, fnP2Supp) = (cutSuppressed(fnP1, supp, p1Args), cutSuppressed(fnP2, supp, p2Args))
      if(fnP1.length != fnP2.length || fnP1Supp.length != fnP2Supp.length) {
        false
      } else {
        val fixed = matchArgs(p1Args, p2Args, (fnP1Supp, fnP2Supp))
        val fnames = new Ref(singles(supp, fixed))

        def foldMatchingComps(as: List[Int], bs: List[Int]): Boolean = {
          (as, bs) match {
            case (Nil, Nil) => true
            case (Nil, _)   => false
            case (a::newAs, _) =>
              val matchingBs = bs.filter({ b => p1.components(a).congruent(fnames)(p2.components(b)) })
              val newBss = matchingBs.map({ matchingB => bs.drop(bs.indexOf(matchingB)) })
              newBss.foldLeft(false)({ (acc, newBs) => acc || foldMatchingComps(newAs, newBs) })
          }
        }
        foldMatchingComps(Range(0, p1.countComponents()).toList, Range(0, p2.countComponents()).toList)

      }
    }
  }
  
  class ProcessElt(val process: Process, val parameters: List[String]) {
    
    def equals(p: ProcessElt): Boolean = {
      Process.congruentN((process, parameters), (p.process, p.parameters))
    }
    
    override def hashCode: Int = {
	    var res = 0
	    val hashVal = 804
	    for(comp <- process.components) {
	      for(fnOut <- comp.freeOutputs) {
	        res += fnOut.continuation + hashVal
	      }
	      for(fnInp <- comp.freeInputs) {
	        res += fnInp.continuation + hashVal
	      }
	      for(bnOut <- comp.boundOutputs) {
	        res += bnOut.continuation + hashVal
	      }
	      for(bnInp <- comp.boundInputs) {
	        res += bnInp.continuation + hashVal
	      }
	      for(test <- comp.idTests) {
	        res += test.tCont + hashVal
	      }
	      for(tau <- comp.actTaus) {
	        res += tau.tauCont + hashVal
	      }
	      for(TopSum(acts, taus, tests) <- comp.actSums) {
	        for(act <- acts) {
	          res += act.continuation + hashVal
	        }
	        for(tau <- taus) {
	          res += tau.tauCont + hashVal
	        }
	        for(test <- tests) {
	          res += test.tCont + hashVal
	        }
	      }
	    }
	    process.components.length * res
	  }
  }

}