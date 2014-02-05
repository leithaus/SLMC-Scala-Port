package biosimilarity.slmc.util

object Namegen {
  val bnInit = "$name"
  val fnInit = "#name"
  var count = 0

  // Determines if a string corresponds to a bound name
  def isBoundAlias(s: String): Boolean = {
    s.substring(0, Math.min(s.length, bnInit.length)).equals(bnInit)
  }

  // Returns a new bound name
  def generateBoundName(): String = {
    val res = bnInit + count
    count += 1
    res
  }

  // Generates a fresh name
  def freshAlias() = {
    val res = fnInit + count
    count += 1
    res
  }
  
  def freshRestrictions(size: Int) = {
    new Array[Any](size).map((_) => generateBoundName())
  }

  def freshAliases(size: Integer): List[String] = {
    for(i <- Range(0, size).toList) yield freshAlias()
  }
}