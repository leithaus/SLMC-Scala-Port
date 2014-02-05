package biosimilarity.slmc.util

object Monoid {
  
  def extend[A,B](f: A => B): List[A] => List[B] = 
    (as) => as.map(f)
    
		def orderedSublists[A](size: Int, list: List[A]): List[List[A]] = {
	    if(size == 0) {
	      Nil
	    }else if(list.length < size) {
	      throw new Exception("Error in orderedSublists: size cannot be larger than input list")
	    } else if(list.length == size) {
	      List(list)
	    } else {
	      list.indices.map(i => list.take(i) ++ list.drop(i+1)).flatMap(orderedSublists(size - 1, _)).toList
	    }
	  }

}