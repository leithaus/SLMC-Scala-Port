package biosimilarity.slmc.util

trait Printable {
  
  def intercalate(sep: String): List[String] => String = {
    case Nil => ""
    case hd::tl =>
      hd + tl.map(sep + _)
  }
  
  def print(s: String) {
    Console.print(s)
  }
  
  def print()

}