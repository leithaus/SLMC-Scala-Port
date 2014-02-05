package biosimilarity.slmc.data.component

import scala.collection.SeqProxy
import biosimilarity.slmc.util.Printable
import biosimilarity.slmc.util.Showable

sealed abstract class Name extends Showable {
  val s = ""
  def show(): String = {
    this match {
      case Bound(s) => "bn(" + s + ")"
      case Free(s) => "fn(" + s + ")"
      case Input(i) => "in(" + i + ")"
    }
  }
}
case class Free(override val s: String) extends Name
case class Bound(override val s: String) extends Name
case class Input(i: Int) extends Name

case class NameSeq(self: List[Name]) extends SeqProxy[Name] with Showable {
  
  def this(self: Name*) = this(self.toList)
  
  def show(): String = {
    intercalate(",")(self.map(_.show()))
  }
  
  def map(f: Name => Name): NameSeq = {
    new NameSeq(self.map(f): _*)
  }
  
  def map[C](f: Name => C): Seq[C] = {
    self.map(f)
  }
  
  def unshift(n: Name): NameSeq = {
    new NameSeq(n::self.toList)
  }
}

object NameSeq {
  def fmap(f: List[Name] => List[Name])(names: NameSeq): NameSeq = {
    NameSeq(f(names.toList))
  }
}