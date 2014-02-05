package biosimilarity.slmc.data.iterator

import scala.collection.mutable.HashMap
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc.{Input => _, _}
import biosimilarity.slmc._
import biosimilarity.slmc.data.Process
import biosimilarity.slmc.data.Process._
import biosimilarity.slmc.data.component._
import biosimilarity.slmc.util.OCaml._
import biosimilarity.slmc.util.Namegen._
import biosimilarity.slmc.data.Equation
import biosimilarity.slmc.data.Equation.{Name => _, Free => _, Input => _, _}
import biosimilarity.slmc.data.Closure._
import biosimilarity.slmc.data.Equation

// Reaction label type
sealed abstract class ReactLabel()
case class RTau() extends ReactLabel
case class RLab(l: ml.Label) extends ReactLabel
case class RName(n: (String, IO)) extends ReactLabel
case class RAction(a: IO) extends ReactLabel

  // Iterator type for reactions
class ReactIterator private(val process: Process, private val iterInfo: Either[IteratorInfo, ReactLabel])
	extends Iterator[Process] {
  
  val info: IteratorInfo =
    iterInfo match {
      case Left(x) => x
      case Right(rl) =>
        rl match {
          case RTau() =>
            TauInfo(new TauIterator(status = FnSynch,
              inputComponent = 0,
              inputIndex = 0,
              outputComponent = 0,
              outputIndex = 0,
              testComponent = 0,
              testIndex = 0,
              tauComponent = 0,
              tauIndex = 0))
          case RLab(ml.Input(channel, arguments)) =>
            val fns = Array.fill[Boolean](0)(false)
            LabelInfo(new LabelIterator(label = ml.Input(channel, arguments),
              													marker = fns,
              													currentComponent = 0,
              													currentIndex = 0))
          case RLab(ml.Output(channel, arguments)) =>
            val fnsP = process.freeNames()
            var i = 0
            val fns = Array.fill[Boolean](arguments.length)(false)
            for (id <- arguments) {
              if (id.equals(" ") || !fnsP.contains(id)) {
                fns(i) = true
                i = i + 1
              }
            }
            LabelInfo(new LabelIterator(label = ml.Output(channel, arguments),
                                        marker = fns,
                                        currentComponent = 0,
                                        currentIndex = 0))
          case RName((n, a)) =>
            NameInfo(new NameIterator(alias = n, actionType = a, component = 0, index = 0))
          case RAction(a) =>
            ActionInfo(new ActionIterator(actionType = a, component = 0, index = 0))
        }
    }
  
  def this(process: Process, info: IteratorInfo) = this(process, Left(info))
  
  def this(process: Process, rl: ReactLabel) = this(process, Right(rl))
  
  private def maybeNext(): Option[Process] = {
          // Auxiliary functions to reactLabel
      def cutComp(p: Process, pos: Int): Process = {
        val compRes = new Array[Component](p.countComponents() - 1)
        for(i <- 0 until p.countComponents() - 1) {
          if(i < pos) {
            compRes(i) = p.components(i)
          } else {
            compRes(i) = p.components(i+1)
          }
        }
        new Process(compRes.toList, p.environment)
      }

      def cutTwoComps(p: Process, pos1: Int, pos2: Int): Process = {
        val compRes = new Array[Component](p.countComponents() - 2)
        val (minPos, maxPos) = (Math.min(pos1, pos2), Math.max(pos1, pos2))
        for(i <- 0 until p.countComponents()-2) {
          compRes(i) =
            if(i < minPos) { 
              p.components(i) 
            } else if(i < maxPos) { 
              p.components(i+1) 
            } else {
              p.components(i+2) 
            }
        }
        new Process(components = compRes.toList, environment = p.environment)
      }

      // Handles the process update after the transition
      def reactLabelAux(p: Process,
                        pos: Int,
                        eq: Equation,
                        act: TopAction,
                        args: List[String],
                        ind: Int,
                        inp: Boolean): Process = {
        
        def reactLabelArgs(inpL: List[String], subArgs: NameSeq): NameSeq = {
          val aux = inpL.toArray
          var res = subArgs.toArray
          for((subArg,i) <- subArgs.zipWithIndex) {
            subArg match {
              case Input(k) => res(i) = Free(aux(k))
              case _ => ;
            }
          }
          new NameSeq(res.toList)
        }
        
        val comp = p.components(pos)
        val marker = Array.fill[Array[Boolean]](eq.actionCount + comp.countActs() - 1)(
          Array.fill[Boolean](eq.restrictionCount + comp.countRestrictions)(false))
        val subArgs = reactLabelArgs(args, act.arguments)
        val subRests = freshRestrictions(eq.restrictionCount)
        val rmarker = comp.restrictionMarkers(eq.restrictionCount, comp.countRestrictions)
        val (os, is, tsts, ts, ss) = eqActs(eq, marker, subArgs, subRests, 0, rmarker, Nil, Nil, Nil, Nil, Nil)
        val freshn = freshAlias()
        val (inpInd, outInd) = if(inp) { (ind,-1) } else { (-1, ind) }
        val (outs, inps, tests, taus, sums) =
        procActs(comp, marker, freshn, freshn, eq.actionCount, rmarker, os, is, tsts, ts, ss, inpInd, outInd, true, -1, -1)
        val (numComps, compActs, compNames) = components(marker)
        val (fnoL, bnoL, fniL, bniL, idTs, actTs, actSs) = createComps(outs, inps, tests, taus, sums, numComps, compActs)
        val rL = new Array[Any](numComps).map((_) => new NameSeq())
        eqRests(compNames, numComps, subRests, eq.restrictionCount, rL, 0)
        procRests(compNames, numComps, comp, comp.countRestrictions, rL, eq.restrictionCount)
        Process(p, numComps, pos, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, actSs)
      }
      
    // Returns a process where an internal transition has taken place
    def reactTau(inpC: Int, inpI: Int, outC: Int, outI: Int, fn: Boolean, p: Process): Process = {
      val (inpAct, outAct) =
        if(fn) {
          (if(inpI < p.components(inpC).nfreeInputs) {
            p.components(inpC).freeInputs(inpI) }
          else {
            getActSums(p.components(inpC).actSums, inpI - p.components(inpC).nfreeInputs, 0) },
          if(outI < p.components(outC).nfreeOutputs) {
            p.components(outC).freeOutputs(outI) }
          else {
            getActSums(p.components(outC).actSums, outI - p.components(outC).nfreeOutputs, 0) })
        } else {
          (if(inpI < p.components(inpC).nboundInputs) {
            p.components(inpC).boundInputs(inpI)
          } else {
          getActSums(p.components(inpC).actSums, inpI - p.components(inpC).nboundInputs, 0) },
          if(outI < p.components(outC).nboundOutputs) {
            p.components(outC).boundOutputs(outI)
          } else
          getActSums(p.components(outC).actSums, outI - p.components(outC).nboundOutputs, 0))
        }
      val inpEq =
        if(inpAct.continuation == voidEquationVariable) { nilEq() } else { p.environment.get(outAct.continuation).get._2 }
      val outEq =
        if(outAct.continuation == voidEquationVariable) { nilEq() } else { p.environment.get(outAct.continuation).get._2 }
        val voidConts =
          inpEq.restrictionCount == 0 && inpEq.actionCount == 0 && outEq.restrictionCount == 0 && outEq.actionCount == 0
        if((voidConts && p.countComponents() == 1 && p.components(0).countActs() == 2) ||
           (p.countComponents() == 2 && p.components(inpC).countActs() == 1 && p.components(outC).countActs() == 1)) {
          new Process()
        } else if(voidConts && inpC == outC && p.components(inpC).countActs == 2) {
          cutComp(p, inpC)
        } else if(voidConts && p.components(inpC).countActs() == 1 && p.components(outC).countActs() == 1) {
          cutTwoComps(p, inpC, outC)
        } else {
          reactTauAux(p, inpC, outC, inpEq, outEq, inpAct, outAct, inpI, outI, fn)
        }
    }
    
    def reactTest(pos: Int, ind: Int, p: Process): Process = {
      val test =
        if(ind < p.components(pos).ntests) {
          p.components(pos).idTests(ind)
        } else {
          getTestSums(p.components(pos).actSums, ind - p.components(pos).ntests, 0)
        }
      if(test.tCont == voidEquationVariable && p.countComponents() == 1 && p.components(pos).countActs() == 1) {
        new Process()
      } else if(test.tCont == voidEquationVariable && p.components(pos).countActs() == 1) {
        cutComp(p, pos)
      } else {
        val testEq =
          if(test.tCont == voidEquationVariable) {
            nilEq()
          } else {
            p.environment.get(test.tCont).get._2
          }
        reactTestAux(p, pos, ind, testEq, test)
      }
    }

    // Returns a process where a tau prefix firing transition has taken place
    def reactTauPref(pos: Int, ind: Int, p: Process): Process = {
      val tau =
        if(ind < p.components(pos).ntaus) {
          p.components(pos).actTaus(ind)
        } else {
          getTauSums(p.components(pos).actSums, ind - p.components(pos).ntaus, 0)
        }
      if(tau.tauCont == voidEquationVariable && p.countComponents() == 1 && p.components(pos).countActs == 1) {
        new Process()
      } else if(tau.tauCont == voidEquationVariable && p.components(pos).countActs() == 1) {
        cutComp(p, pos)
      } else {
        val tauEq =
          if(tau.tauCont == voidEquationVariable) {
            nilEq()
          } else {
            p.environment.get(tau.tauCont).get._2
          }
        reactTauPrefAux(p, pos, ind, tauEq, tau)
      }
    }

        
    // Returns a process where a transition on a subject name or action type has taken place
    def nextReactAux(p: Process, actT: IO, comp: Int, ind: Int): Process = {
      if(actT == Equation.Input) {
        val act =
          if(ind < p.components(comp).nfreeInputs()) {
            p.components(comp).freeInputs(ind)
          } else {
            getActSums(p.components(comp).actSums, (ind - p.components(comp).nfreeInputs()), 0)
          }
          reactLabel(comp, ind, p)(ml.Input(act.subject.s, freshAliases(act.objects.length)))
      } else {
        val act =
          if(ind < p.components(comp).nfreeOutputs()) {
            p.components(comp).freeOutputs(ind)
          } else {
            getActSums(p.components(comp).actSums, (ind - p.components(comp).nfreeOutputs()), 0)
          }
        reactLabel(comp, ind, p)(ml.Input(act.subject.s, act.objects.map((n: Name) => n.s).toList))
      }
    }


    // Handles the process update after the synchronization
    def reactTauAux(p: Process,
                    inpC: Int,
                    outC: Int,
                    inpEq: Equation,
                    outEq: Equation,
                    inpAct: TopAction,
                    outAct: TopAction,
                    inpI: Int,
                    outI: Int,
                    fn: Boolean): Process = {
     
      def reactTauArgs(inpL: NameSeq, subArgs: NameSeq): NameSeq = {
        val res = subArgs.toArray
        for((subArg, i) <- subArgs.zipWithIndex) {
          subArg match {
            case Input(k) => res(i) = inpL(k)
            case _ => ;
          }
        }
        new NameSeq(res.toList)
      }
      
      val inpComp = p.components(inpC)
      val outComp = p.components(outC)
      val (numActs, numRests) =
        if(inpC != outC) {
          ((inpEq.actionCount + outEq.actionCount + p.components(inpC).countActs() + p.components(outC).countActs() - 2),
            (inpEq.restrictionCount + outEq.restrictionCount + (inpComp.countRestrictions) + (outComp.countRestrictions)))
        } else {
          ((inpEq.actionCount + outEq.actionCount + p.components(inpC).countActs() - 2),
            (inpEq.restrictionCount + outEq.restrictionCount + (inpComp.countRestrictions)))
        }
      val marker = Array.fill[Array[Boolean]](numActs)(Array.fill[Boolean](numRests)(false))
      val inpSubArgs = reactTauArgs(outAct.objects, inpAct.arguments)
      val outSubArgs = outAct.arguments
      val inpSubRests = freshRestrictions(inpEq.restrictionCount)
      val outSubRests = freshRestrictions(outEq.restrictionCount)
      var rmarker = inpComp.restrictionMarkers(inpEq.restrictionCount + outEq.restrictionCount, inpComp.countRestrictions)
      if (inpC != outC) {
        rmarker = rmarker ++ outComp.restrictionMarkers(inpEq.restrictionCount + outEq.restrictionCount + inpComp.countRestrictions, outComp.countRestrictions)
      }
      val (os1, is1, tsts1, ts1, ss1) = eqActs(inpEq, marker, inpSubArgs, inpSubRests, 0, rmarker, Nil, Nil, Nil, Nil, Nil)
      if(outEq.restrictionCount > 0) {
        for(i <- (inpEq.restrictionCount - 1) to 0) {
          for(j <- 0 until inpEq.restrictionCount) {
            marker(j)(i + outEq.restrictionCount) = marker(j)(i)
          }
        }
      }
      val (os2, is2, tsts2, ts2, ss2) =
        eqActs(outEq, marker, outSubArgs, outSubRests, inpEq.restrictionCount, rmarker, os1, is1, tsts1, ts1, ss1)
      val freshn = freshAlias()
      val startAct = inpEq.restrictionCount + outEq.restrictionCount
      val (outs, inps, tests, taus, sums) =
        if(inpC != outC) {
          val (os3, is3, tsts3, ts3, ss3) =
            procActs(inpComp, marker, freshn, freshn, startAct, rmarker, os2, is2, tsts2, ts2, ss2, inpI, -1, fn, -1, -1)
          procActs(comp = outComp,
                  marker = marker,
                  oldn = freshn,
                  revn = freshn,
                  startAct = startAct + p.components(inpC).countActs() - 1,
                  rmarker = rmarker, 
                  startOuts = !os3,
                  startInps = !is3,
                  startTests = !tsts3,
                  startTaus = !ts3,
                  startSums = !ss3,
                  inpInd = -1,
                  outInd = outI,
                  fn = fn,
                  ti = -1,
                  taui = -1)
            
//          procActs(outComp, marker, freshn, freshn, startAct + p.components(inpC).countActs() - 1, rmarker, !os3, !is3, !tsts3, !ts3, !ss3, -1, outI, fn, -1, -1)
        } else {
          procActs(inpComp, marker, freshn, freshn, startAct, rmarker, os2, is2, tsts2, ts2, ss2, inpI, outI, fn, -1, -1)
        }
      val (numComps, compActs, compNames) = components(marker)
      val (fnoL, bnoL, fniL, bniL, idTs, actTs, actSs) = createComps(outs, inps, tests, taus, sums, numComps, compActs)
      val rL = new Array[Any](numComps).map((_) => new NameSeq())
      eqRests(compNames, numComps, outSubRests, outEq.restrictionCount, rL, 0)
      eqRests(compNames, numComps, inpSubRests, inpEq.restrictionCount, rL, outEq.restrictionCount)
      val startRests = outEq.restrictionCount + inpEq.restrictionCount
      if(inpC != outC) {
        procRests(compNames, numComps, outComp, outComp.countRestrictions, rL, startRests + inpComp.countRestrictions)
        Process(p, numComps, inpC, outC, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, actSs)
      } else {
        Process(p, numComps, inpC, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, actSs)
      }
    }



    // Handles the process update after the ttest firing transition
    def reactTestAux(p: Process, pos: Int, ind: Int, eq: Equation, test: TopTest): Process = {
      val comp = p.components(pos)
      val marker = Array.fill[Array[Boolean]](eq.actionCount + p.components(pos).countActs() - 1)(Array.fill[Boolean](eq.restrictionCount + comp.countRestrictions)(false))
      val subArgs = test.tArgs
      val subRests = freshRestrictions(eq.restrictionCount)
      val rmarker = comp.restrictionMarkers(eq.restrictionCount, comp.countRestrictions)
      val (os, is, tsts, ts, ss) = eqActs(eq, marker, subArgs, subRests, 0, rmarker, Nil, Nil, Nil, Nil, Nil)
      val freshn = freshAlias()
      val (outs, inps, tests, taus, sums) =
        procActs(comp, marker, freshn, freshn, eq.actionCount, rmarker, os, is, tsts, ts, ss, -1, -1, true, ind, -1)
      val (numComps, compActs, compNames) = components(marker)
      val (fnoL, bnoL, fniL, bniL, idTs, actTs, inpSs) = createComps(outs, inps, tests, taus, sums, numComps, compActs)
      val rL = new Array[Any](numComps).map((_) => new NameSeq())
      eqRests(compNames, numComps, subRests, eq.restrictionCount, rL, 0)
      procRests(compNames, numComps, comp, comp.countRestrictions, rL, eq.restrictionCount)
      Process(p, numComps, pos, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, inpSs)
    }


    // Auxiliary function to reactTest
    def getTestSums(sums: TopSumSeq, ind: Int, i: Int): TopTest = {
      def getTestSums: (List[TopSum], Int) => TopTest = {
        case (Nil, _) => throw new Error()
        case (TopSum(acts, taus, tests)::tl, i) =>
          if(ind < tests.length + i) {
            getPosSum(tests, ind, i)
          } else {
            getTestSums(tl, i + tests.length)
          }
      }
      getTestSums(sums.toList, i)
    }

    // Handles the process update after the a tau prefix firing
    def reactTauPrefAux(p: Process, pos: Int, ind: Int, eq: Equation, tau: TopTau): Process = {
      val comp = p.components(pos)
      val marker = Array.fill[Array[Boolean]](eq.actionCount + p.components(pos).countActs())(Array.fill[Boolean](eq.restrictionCount + comp.countRestrictions)(false))
      val subArgs = tau.tauArgs
      val subRests = freshRestrictions(eq.restrictionCount)
      val rmarker = comp.restrictionMarkers(eq.restrictionCount, comp.countRestrictions)
      val (os, is, tsts, ts, ss) = eqActs(eq, marker, subArgs, subRests, 0 , rmarker, Nil, Nil, Nil, Nil, Nil)
      val freshn = freshAlias()
      val (outs, inps, tests, taus, sums) =
        procActs(comp, marker, freshn, freshn, eq.actionCount, rmarker, os, is, tsts, ts, ss, -1, -1, true, -1, ind)
      val (numComps, compActs, compNames) = components(marker)
      val (fnoL, bnoL, fniL, bniL, idTs, actTs, inpSs) = createComps(outs, inps, tests, taus, sums, numComps, compActs)
      val rL = new Array[Any](numComps).map((_) => new NameSeq())
      eqRests(compNames, numComps, subRests, eq.restrictionCount, rL, 0)
      procRests(compNames, numComps, comp, comp.countRestrictions, rL, eq.restrictionCount)
      Process(p, numComps, pos, rL, fnoL, bnoL, fniL, bniL, idTs, actTs, inpSs)
    }

    
    // Returns a process where a transition on a given label has taken place
    def reactLabel[A](pos: Int, ind: Int, p: Process): ml.Label => Process = {
      case (ml.Input(channel, arguments)) =>
      	val comp = p.components(pos)
        val (act, inp) =
          if(ind < comp.nfreeInputs) {
            (comp.freeInputs(ind), true)
          } else {
            (getActSums(comp.actSums, ind - comp.nfreeInputs, 0), true)
          }
	      if(act.continuation == voidEquationVariable) {
	        if(p.countComponents() == 1) {
	          new Process()
	        } else {
	          cutComp(p, pos)
	        }
	      } else {
	        val eq = p.environment.get(act.continuation).get._2
	        reactLabelAux(p, pos, eq, act, arguments, ind, inp)
	      } 
      case (ml.Output(channel, arguments)) =>
        val comp = p.components(pos)
        val (act, inp) =
          if(ind < comp.nfreeOutputs) {
            (comp.freeOutputs(ind), false)
          } else {
            (getActSums(comp.actSums, ind - comp.nfreeOutputs, 0), false)
          }
	      if(act.continuation == voidEquationVariable) {
	        if(p.countComponents() == 1) {
	          new Process()
	        } else {
	          cutComp(p, pos)
	        }
	      } else {
	        val eq = p.environment.get(act.continuation).get._2
	        reactLabelAux(p, pos, eq, act, arguments, ind, inp)
	      } 
    }

    info match {
      case LabelInfo(i) =>
        val (notFound, comp, ind, reveals) =
          findLabel(process, i.label, i.currentComponent, i.currentIndex, i.marker)
        if (notFound) {
          return None
        }
        i.currentComponent = comp
        i.currentIndex = ind + 1
        val ptrP = new Ref(process)
        val resNameComp = new Ref(comp)
        val resNameInd = new Ref(ind)

        for (arg <- reveals) {
          val (newn, oldn) = arg
          val oldNComps = (!ptrP).countComponents()
          val restInd = findRest(!ptrP, !resNameComp, oldn)
          ptrP := revealComponents(!resNameComp, restInd, newn)(!ptrP)
          val (newNameComp, newNameInd) = findNewPos(!ptrP, oldNComps, !resNameInd)
          resNameComp := newNameComp
          resNameInd := newNameInd
        }

        Some(reactLabel(!resNameComp, !resNameInd, !ptrP)(i.label))
      case TauInfo(i) =>
        if (i.status == FnSynch) {
          val (notFound, inputComponent, inputIndex, outputComponent, outputIndex) =
            findFnTau(process, i.inputComponent, i.inputIndex, i.outputComponent, i.outputIndex)

          if (notFound) {
            i.status = BnSynch
            i.inputComponent = 0
            i.inputIndex = 0
            i.outputComponent = 0
            i.outputIndex = 0
            maybeNext()
          } else {
            i.inputComponent = inputComponent
            i.inputIndex = inputIndex
            i.outputComponent = outputComponent
            i.outputIndex = outputIndex + 1
            Some(reactTau(i.inputComponent, i.inputIndex, i.outputComponent, outputIndex, true, process))
          }
        } else {
          if (i.status == BnSynch) {
            val (notFound, comp, inputIndex, outputIndex) =
              findBnTau(process, i.inputComponent, i.inputIndex, i.outputIndex)

            if (notFound) {
              i.status = TestAct
              maybeNext()
            } else {
              i.inputComponent = comp
              i.inputIndex = inputIndex
              i.outputIndex = outputIndex + 1
              Some(reactTau(i.inputComponent, i.inputIndex, i.inputComponent, outputIndex, false, process))
            }
          } else {
            if (i.status == TestAct) {
              val (found, comp, ind) =
                findTest(process, i.testComponent, i.testIndex)
              if (!found) {
                i.status = TauAct
                maybeNext()
              } else {
                i.testComponent = comp
                i.testIndex = ind + 1
                Some(reactTest(comp, ind, process))
              }
            } else {
              val (found, comp, ind) =
                findTauPref(process, i.tauComponent, i.tauIndex)
              if (!found) {
                return None
              }
              i.tauComponent = comp
              i.tauIndex = ind + 1
              Some(reactTauPref(comp, ind, process))
            }
          }
        }
      case NameInfo(i) =>
        val (found, comp, ind, reveals) =
          findName(process, i.alias, i.actionType, i.component, i.index)

        if (!found) {
          return None
        }
        i.component = comp
        i.index = ind + 1
        val ptrP = new Ref(process)
        val resNameComp = new Ref(comp)
        val resNameInd = new Ref(ind)

        for ((newn, oldn) <- reveals) {
          val oldNcomps = (!ptrP).countComponents()
          val restInd =
            findRest(!ptrP, !resNameComp, oldn)

          ptrP := revealComponents(!resNameComp, restInd, newn)(!ptrP)
          val (newNameComp, newNameInd) =
            findNewPos(!ptrP, oldNcomps, !resNameInd)
          resNameComp := newNameComp
          resNameInd := newNameInd
        }
        Some(nextReactAux(!ptrP, i.actionType, !resNameComp, !resNameInd))
      case ActionInfo(i) =>
        val (found, comp, ind, reveals) =
          findAction(process, i.actionType, i.component, i.index)
        if (!found) {
          return None
        }
        i.component = comp
        i.index = ind + 1
        val ptrP = new Ref(process)
        val resNameComp = new Ref(comp)
        val resNameInd = new Ref(ind)

        for ((newn, oldn) <- reveals) {
          val oldNcomps = (!ptrP).countComponents()
          val restInd = findRest(!ptrP, !resNameComp, oldn)

          ptrP := revealComponents(!resNameComp, restInd, newn)(!ptrP)
          val (newNameComp, newNameInd) = findNewPos(!ptrP, oldNcomps, !resNameInd)
          resNameComp := newNameComp
          resNameInd := newNameInd
        }
        Some(nextReactAux(!ptrP, i.actionType, !resNameComp, !resNameInd))
    }
  }
  
  var buf = maybeNext()
  
  def hasNext(): Boolean = {
    buf match {
      case Some(_) => true
      case None => false
    }
  }
  
  def next(): Process = {
    buf match {
      case Some(p) => 
        buf = maybeNext()
        p
      case None => throw new Exception()
    }
  }
}