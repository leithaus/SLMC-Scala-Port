package biosimilarity.slmc.data.component

import scala.collection.SeqProxy
import biosimilarity.slmc.util.Printable

case class TopSum(acts: TopActionSeq, taus: TopTauSeq, tests: TopTestSeq) extends Printable {
  def print() {
    def printPlusIf(p: Boolean) {
      if (p) {
        print("+ ")
      }
    }
    acts.print()
    printPlusIf(acts.length > 0 && taus.length > 0)
    taus.print()
    printPlusIf(acts.length + taus.length > 0 && tests.length > 0)
    tests.print()
  }
}

class TopSumSeq(self: TopSum*) extends SeqProxy[TopSum] with Printable {
  
  def self() = self
  
  def print() {
    self.toList match {
      case Nil => ;
      case sum::Nil =>
        sum.print()
      case sum::tl =>
        sum.print()
        tl.foreach((sum) => {
        println()
        sum.print() })
    }
  }
  
  def unshift(t: TopSum): TopSumSeq = {
    new TopSumSeq((t::self.toList): _*)
  }
}