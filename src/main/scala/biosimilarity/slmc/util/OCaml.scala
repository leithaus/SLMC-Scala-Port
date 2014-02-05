package biosimilarity.slmc.util

import scala.collection.mutable.HashMap

object OCaml {

  class Ref[A](var value: A) {

    def :=(newVal: A) {
      value = newVal
    }

    def unary_! = value
  }

  def incr(ref: Ref[Int]) {
    ref := !ref + 1
  }

  def decr(ref: Ref[Int]) {
    ref := !ref - 1
  }

  // Warning: Importing Hashtbl.find to match behaviors doesn't make the code better.  Refactor in optimization.
  case class NotFound(msg: String = "Not_found") extends Exception
  def hashtblFind[A,B](h: HashMap[A, B], k:A): B =
    h.get(k) match {
      case Some(v) => v
      case None => throw new NotFound()
    }

}