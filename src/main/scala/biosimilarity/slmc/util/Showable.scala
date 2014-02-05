package biosimilarity.slmc.util

trait Showable extends Printable {
  
  def show(): String
  
  def print() {
    print(show())
  }
    
	object VarArg {
	  def unapply(vararg: List[String]): Option[String] = 
	    vararg match {
	      case Nil =>
	        Some("")
	      case hd::tl =>
	        Some("(%s,%s)".format(hd, intercalate(",")(tl)))
	    }
	}

}