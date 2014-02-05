package biosimilarity.slmc.data.iterator
  
import scala.collection.mutable.HashMap

import biosimilarity.slmc.util.OCaml._
import biosimilarity.slmc.data.component.Component
import biosimilarity.slmc.data._
import biosimilarity.slmc.data.Equation

// Iterator type for composition
class CompositionIterator (val process: Process) extends Iterator[(Process, Process)] {
  var status: IteratorStatus =
    if (process.countComponents() == 1) {
      Dummy(process.isEmpty())
    } else {
      NotFinished
    }
  var number: Int = 1
  var components: List[Int] = List(process.countComponents() - 1)
    
    

  // Returns the iterator's next composition of processes
  private def maybeNext(): Option[(Process, Process)] = {
    
    println("next_comp for process")
    process.print()
    
	  def lastPos(k: Int, l: List[Int]): Boolean = {
	    def lastPos(k: Int, l: List[Int]): Boolean = {
		    l match {
		      case Nil => false
		      case List(hd) => hd == k
		      case hd :: tl => hd == k && lastPos(k + 1, tl)
		    }
	    }
	    val res = lastPos(k, l)
	    println("lastPos: " + l + " ==> " + res)
	    res
	  }
	
	  def createList(end: Int, length: Int): List[Int] = {
	    Range(end-length,end,1).toList
	  }
	
	  def decList(l: List[Int]): List[Int] = {
	    val k = new Ref(0)
		  def decList(l: List[Int]): List[Int] = {
		    l match {
		      case Nil => Nil
		      case List(hd) =>
		        k := hd - 2
		        List(hd - 1)
		      case hd::tl =>
		        if (hd > !k) {
		          k := hd - 2
		          (hd - 1)::tl
		        } else {
		          k := !k + 1
		          val ntl = decList(tl)
		          val nhd = !k
		          k := !k - 1
		          nhd::ntl
		        }
		    }
		  }
	    decList(l)
	  }
	  
	  def info(size: Int) {
	    val last = lastPos(0, components)
	
	    if (last && (number == size - 1)) {
	      println("declaring last")
	      status = Dummy(false)
	    } else {
	      if (last) {
	        println("incrementing number")
	        number = number + 1
	        components = createList(size - 1, number)
	      } else {
	        println("declaring new list")
	        components = decList(components)
	      }
	    }
	  }

    // Builds two processes by separating an existing one
    def extractComps(p: Process, is: List[Int], size: Int, dim1: Int, dim2: Int): (Process, Process) = {
      var j = 0
      var k = 0
      val p1Comps = Array.fill[Component](dim1)(new Component())
      val p2Comps = Array.fill[Component](dim2)(new Component())
      for(i <- 0 until size) {
        if(is.contains(i)) {
          p1Comps(j) = p.components(i)
          j = j + 1
        } else {
          p2Comps(k) = p.components(i)
          k = k + 1
        }
      }
      val p1 = new Process(p1Comps.toList, p.environment)
      val p2 = new Process(p2Comps.toList, p.environment)
      (p1, p2)
    }

    // Builds a pair of processes by composing with the empty process
    def compEmpty(p: Process, left: Boolean): (Process, Process) = {
      val empty = new Process(components = List(new Component()), environment = Map())
      if(left) { (empty, p) } else { (p, empty) }
    }

    /** Finds a component that holds restrictions */
    def findRestrictedComponent(p: Process, start: Int = 0): Int = {
      for(i <- Range(start, p.countComponents())) {
        if(p.components(i).countRestrictions > 0) {
          return i
        }
      }
      p.countComponents()
    }
    
    status match {
      case NotFinished =>
        println("getting next comp")
        val size = process.countComponents()
        val compNum = number
        val nl = components

        info(size)
        Some(extractComps(process, nl, size, number, size - compNum))
      case Dummy(b) =>
        println("getting next comp")
        if (b) {
          status = Finished
          Some(compEmpty(process, true))
        } else {
          status = Dummy(true)
          Some(compEmpty(process, false))
        }
      case Finished => 
        println("no more comps")
        None
    }
  }
  
  def hasNext(): Boolean = {
    status match {
      case NotFinished => true
      case Dummy(b) => true
      case Finished => false
    }
  }
  
  def next(): (Process, Process) = {
    maybeNext() match {
      case Some(p) => p
      case None => throw new Exception("undefined call to CompositionIterator.next()")
    }
  }
}