package biosimilarity.slmc.util

import scala.collection.mutable
import scala.collection.immutable
import biosimilarity.slmc.util.OCaml.NotFound

  /** Simple OCaml Hashtbl implementation for add/remove semantics */
  class Environment[A, B]private (val table: mutable.Map[A, List[B]]) {
  
    def this() = this(mutable.Map[A, List[B]]())
    def this(seed: immutable.Map[A,B]) = this(mutable.Map() ++ seed.mapValues(_::Nil))
    
    def add(k: A, v: B) = table.put(k, v::table.getOrElse(k, Nil))
    
    def remove(k: A) =
      table.getOrElse(k, Nil) match {
      case Nil => ;
      case hd::tl => table.put(k, tl)
    }
    
    def mem(k: A) =
      table.getOrElse(k, Nil) match {
      case Nil => false
      case _ => true
    }
    
    def find(k: A) =
      table.getOrElse(k, Nil) match {
      case Nil => throw new NotFound()
      case hd::tl => hd
    }
    
    /** Hack! */
    def getOrElse(k: A, default: B) = 
      table.getOrElse(k, Nil) match {
      case Nil => default
      case hd::tl => hd
    }
    
    def mapValues[C](f: B => C): Environment[A,C] =
      new Environment(mutable.Map() ++ table.mapValues(Monoid.extend(f)))
    
    def toMap(): immutable.Map[A,B] = {
      table.filter({ case (_,v) => !v.isEmpty }).mapValues(_.head).toMap
    }
  }

object Environment {
  def fromMap[A,B](seed: mutable.Map[A,B]) = new Environment[A,B](mutable.Map() ++ seed.mapValues(_::Nil))
}