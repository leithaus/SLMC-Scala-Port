package biosimilarity.slmc.data.component

import scala.collection.SeqProxy
import biosimilarity.slmc.data.Equation._
import biosimilarity.slmc.util.Showable
import biosimilarity.slmc.ast.pc

// Top level process test prefix type
class TopTest(val tst: pc.TestType,
              val idl: Name,
              val idr: Name,
              val tCont: Variable,
              val tArgs: NameSeq) extends Showable {

  def show(): String = {
    if (tst == pc.Equals) {
      "[" + idl.show() + "=" + idr.show() + "]." + tCont + "(" + tArgs.show() + ")\n"
    } else {
      "[" + idl.show() + "!=" + idr.show() + "]." + tCont + "(" + tArgs.show() + ")\n"
    }
  }
}

class TopTestSeq(self: TopTest*) extends SeqProxy[TopTest] with Showable {
  
  def self() = self
  
  def show(): String = {
    intercalate(",")(self.toList.map(_.show()))
  }
  
  def unshift(t: TopTest): TopTestSeq = {
    new TopTestSeq(t::self.toList: _*)
  }
}