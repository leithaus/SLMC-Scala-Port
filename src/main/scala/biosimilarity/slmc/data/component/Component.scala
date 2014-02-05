package biosimilarity.slmc.data.component

import scala.collection.SeqProxy
import scala.collection.mutable.HashMap
import biosimilarity.slmc.data.Equation._
import biosimilarity.slmc.util.Namegen._
import biosimilarity.slmc.util.OCaml.Ref
import biosimilarity.slmc.util.Printable
import biosimilarity.slmc.util.Showable

case object False extends Exception
case object Found extends Exception
case object Error extends Exception
case object FoundFn extends Exception

// Action kind type
abstract class ActKind
case class ActK(act: TopAction) extends ActKind
case class TauK(tau: TopTau) extends ActKind
case class TestK(test: TopTest) extends ActKind
case class SumK(sum: TopSum) extends ActKind

// Top level process component type
class Component(val restrictions: Seq[Name],
                val freeOutputs: TopActionSeq,
                val boundOutputs: TopActionSeq,
                val freeInputs: TopActionSeq,
                val boundInputs: TopActionSeq,
                val idTests: TopTestSeq,
                val actTaus: TopTauSeq,
                val actSums: TopSumSeq) extends Printable  {
         
  /** Nil constructor */
  def this() =
    this(new Array[Name](0),
         new TopActionSeq,
         new TopActionSeq,
         new TopActionSeq,
         new TopActionSeq,
         new TopTestSeq,
         new TopTauSeq,
         new TopSumSeq)

  def countRestrictions() = restrictions.length
  def nfreeOutputs() = freeOutputs.length
  def nboundOutputs() = boundOutputs.length
  def nfreeInputs() = freeInputs.length
  def nboundInputs() = boundInputs.length
  def ntests() = idTests.length
  def ntaus() = actTaus.length
  def nsums() = actSums.length

  def countActs(): Int = {
    nfreeOutputs + nfreeInputs + nboundOutputs + nboundInputs + ntests + ntaus + nsums
  }
  
  def selectAct(i: Int): ActKind = {
    var x = i
    if(x < nfreeOutputs()) {
      ActK(freeOutputs(x))
    } else {
      x -= nfreeOutputs()
      if(x < nboundOutputs()) {
        ActK(boundOutputs(x))
      } else {
        x -= nboundOutputs()
        if(x < nfreeInputs()) {
          ActK(freeInputs(x))
        } else {
          x -= nfreeInputs()
          if(x < nboundInputs()) {
            ActK(boundInputs(x))
          } else {
            x -= nboundInputs()
            if(x < ntests()) {
              TestK(idTests(x))
            } else {
              x -= ntests()
              if(x < ntaus()) {
                TauK(actTaus(x))
              } else {
                SumK(actSums(x-ntaus()))
              }
            }
          }
        }

      }
    }
  }
  
  def congruent(fnames: Ref[List[(List[String], List[String])]])(c: Component): Boolean = {

    val testNums = 
      (countRestrictions() == c.countRestrictions()
      && nfreeOutputs() == c.nfreeOutputs()
      && nboundOutputs() == c.nboundOutputs()
      && nfreeInputs() == c.nfreeInputs()
      && nboundInputs() == c.nboundInputs()
      && ntests() == c.ntests()
      && nsums == c.nsums())

	  // Determines if two actions are equivalent
	  def isCongNAct(k1: ActKind, k2: ActKind, fnames: Ref[List[(List[String], List[String])]], rests: Ref[List[(List[String], List[String])]]): Boolean = {
	    
		  def related[A](n1: A, n2: A, l: List[(List[A], List[A])]): (List[(List[A], List[A])], Boolean) = {
		    
		    def cutElem[A](el: A, l: List[A]): List[A] = {
		      l.filter(x => x == el)
		    }
		    
		    l match {
		      case Nil => (Nil, n1 == n2)
		      case (ns1, ns2)::tl =>
		        if(ns1.contains(n1)) {
		          if(ns2.contains(n2)) {
		            if(ns1.length == 1) {
		              ((List(n1), List(n2))::tl, true)
		            } else {
		              ((List(n1), List(n2))::(cutElem(n1, ns1), cutElem(n2, ns2))::tl,true)
		            }
		          } else {
		            ((ns1, ns2)::tl, false)
		          }
		        } else {
		          if(ns2.contains(n2)) {
		            ((ns1, ns2)::tl, false)
		          } else {
		            val (resL, res) = related(n1, n2, tl)
		            ((ns1, ns2)::resL, res)
		          }
		        }
		    }
		  }
	
	    def relateName(n1: Name, n2: Name, fnames: Ref[List[(List[String], List[String])]], rests: Ref[List[(List[String], List[String])]]): Boolean = {
	      (n1, n2) match {
	        case (Free(fn1), Free(fn2)) =>
	          val (resL, res) = related(fn1, fn2, !fnames)
	          fnames := resL
	          res
	        case (Bound(bn1), Bound(bn2)) =>
	          val (resL, res) = related(bn1, bn2, !rests)
	          rests := resL
	          res
	        case (Input(i), Input(k)) =>
	          i == k
	        case _ => false
	      }
	    }
	
	    def relateNameL(l1: NameSeq, l2: NameSeq, fnames: Ref[List[(List[String], List[String])]], rests: Ref[List[(List[String], List[String])]]): Boolean = {
	      l1.zip(l2).foldLeft(true)((acc, args) => acc && relateName(args._1, args._2, fnames, rests))
	    }
	    
	    
	    (k1, k2) match {
	      case (ActK(act1), ActK(act2)) =>
	        (act1.objects.length == act2.objects.length
	        && act1.continuation == act2.continuation
	        && act1.arguments.length == act2.arguments.length
	        && relateName(act1.subject, act2.subject, fnames, rests)
	        && relateNameL(act1.objects, act2.objects, fnames, rests)
	        && relateNameL(act1.arguments, act2.arguments, fnames, rests))
	      case (TauK(tau1), TauK(tau2)) =>
	        (tau1.tauCont == tau2.tauCont
	        && tau1.tauArgs.length == tau2.tauArgs.length
	        && relateNameL(tau1.tauArgs, tau2.tauArgs, fnames, rests))
	      case (TestK(test1), TestK(test2)) =>
	        (test1.tCont == test2.tCont
	        && test1.tArgs.length == test2.tArgs.length
	        && ((test1.idl == test2.idl) == (test1.idr == test2.idr))
	        && relateNameL(test1.tArgs, test2.tArgs, fnames, rests))
	      case (SumK(TopSum(acts1, taus1, tests1)), SumK(TopSum(acts2, taus2, tests2))) =>
	        def foldMatchingActs(as: TopActionSeq, bs: TopActionSeq): Boolean = {
	          (as.toList, bs.toList) match {
	            case (Nil, Nil) => true
	            case (Nil, _)   => false
	            case (a::newAs, _) =>
	              val matchingBs = bs.filter({ x => isCongNAct(ActK(a), ActK(x), fnames, rests) })
	              val newBss = matchingBs.map({ matchingB => bs.drop(bs.indexOf(matchingB)) })
	              newBss.foldLeft(false)({ (acc, newBs) => acc || foldMatchingActs(newAs.asInstanceOf, newBs.asInstanceOf) })
	          }
	        }
	        foldMatchingActs(acts1, acts2)
	    }
	  }
	
	  def getStrings(l: List[Name]): List[String] = 
	    l.map(_.s)
  
    if(!testNums) {
      false
    } else {
      val rests = new Ref(List((getStrings(restrictions.toList), getStrings(c.restrictions.toList))))
      val acts1 = Range(0, countActs).map(selectAct(_)).toList
      val acts2 = Range(0, c.countActs).map(c.selectAct(_)).toList
      def foldMatchingActs(as: List[ActKind], bs: List[ActKind]): Boolean = {
        (as, bs) match {
          case (Nil, Nil) => true
          case (Nil, _)   => false
          case (a::newAs, _) =>
            val matchingBs = bs.filter({ b => isCongNAct(a, b, fnames, rests) })
            val newBss = matchingBs.map({ matchingB => bs.drop(bs.indexOf(matchingB)) })
            newBss.foldLeft(false)({ (acc, newBs) => acc || foldMatchingActs(newAs, newBs) })
        }
      }
      foldMatchingActs(acts1, acts2)
    }
  }
  
  // Restricted name update identification
  def restrictionMarkers(startRestriction: Int, position: Int): HashMap[String, Int] = {
    val res = new HashMap[String, Int]()
    var count = startRestriction
    for(i <- 0 until countRestrictions) {
      if(i != position) {
        res.put(restrictions(i).s, count)
        count = count + 1
      }
    }
    res
  }
  
  def show(): String = {
    var res = ""
      
    def show[A](header: String, count: Option[Int], c: Iterable[Showable]) {
      res += header + ": "
      if (count != None) {
        res += count.get
      }
      res += "\n"
      for (elt <- c) {
        res += elt.show() + "\n"
      }
    }

    println("- COMP -")
    show("restricted", None, restrictions)
    show("fnouts", Some(nfreeOutputs), freeOutputs)
    show("fninps", Some(nfreeInputs), freeInputs)
    show("bnouts", Some(nboundOutputs), boundOutputs)
    show("bninps", Some(nboundInputs), boundInputs)
    show("taus",  Some(ntaus), actTaus)
    show("tests", Some(ntests), idTests)
    res
  }
  
  def print() {
    def show[A](header: String, count: Option[Int], c: Iterable[Printable]) {
      print(header + ": ")
      if (count != None) {
        println(count.get)
      } else {
        println
      }
      for (elt <- c) {
        elt.print(); println
      }
    }

    println("- COMP -")
    show("restricted", None, restrictions)
    show("fnouts", Some(nfreeOutputs), freeOutputs)
    show("fninps", Some(nfreeInputs), freeInputs)
    show("bnouts", Some(nboundOutputs), boundOutputs)
    show("bninps", Some(nboundInputs), boundInputs)
    show("taus",  Some(ntaus), actTaus)
    show("tests", Some(ntests), idTests)

    print("sums: " + nsums + "\n")
    actSums.print()
  }
}