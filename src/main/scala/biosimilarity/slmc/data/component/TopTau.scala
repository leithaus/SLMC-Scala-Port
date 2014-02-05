package biosimilarity.slmc.data.component

import scala.collection.SeqProxy
import biosimilarity.slmc.data.Equation._
import biosimilarity.slmc.util.Showable

// Top level process internal action type
class TopTau(val tauCont: Variable,
             val tauArgs: NameSeq) extends Showable {
  
  def show(): String = {
    "tau." + tauCont + "(" + tauArgs.show() + ")\n"
  }
}
  
class TopTauSeq(self: TopTau*) extends SeqProxy[TopTau] with Showable {
  
  def self() = self
  
  def show(): String = {
    intercalate(",")(self.toList.map(_.show()))
  }
  
  def unshift(t: TopTau): TopTauSeq = {
    new TopTauSeq(t::self.toList: _*)
  }
}