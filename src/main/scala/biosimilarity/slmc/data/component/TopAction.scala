package biosimilarity.slmc.data.component

import scala.collection.SeqProxy

import biosimilarity.slmc.data.Equation._
import biosimilarity.slmc.util.Showable

class TopAction(val actionType: IO,
             val subject: Name,
             val objects: NameSeq,
             val continuation: Variable,
             val arguments: NameSeq) extends Showable {
  def isFnAct(): Boolean = {
    subject match {
      case Free(_) => true
      case _ => false
    }
  }
  

  def show(): String = {
    var res = ""
    res += subject.show()
    if (actionType == Output) {
      res += "!("
    } else {
      res += "?("
    }
    res += objects.show() + ").X" + continuation + "(" + arguments.show() + ")"
    res
  }
  
}

class TopActionSeq(self: TopAction*) extends SeqProxy[TopAction] with Showable {
  
  def self() = self

  def show(): String = {
  		intercalate(",")(self.toList.map(_.show())) 
  }
  
  def unshift(t: TopAction): TopActionSeq = {
    new TopActionSeq(t::self.toList: _*)
  }
  
}