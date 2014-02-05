package biosimilarity.slmc.data.iterator
// Module that handles the search algorithms for process inspections
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.pc.PiCalculus
import biosimilarity.slmc.data.Process
import biosimilarity.slmc.data.Process._
import biosimilarity.slmc.util.OCaml._
import biosimilarity.slmc.data.Equation.IO

// Iterator status type
sealed abstract class IteratorStatus()
case object NotFinished extends IteratorStatus
case class Dummy(b: Boolean) extends IteratorStatus
case object Finished extends IteratorStatus

// Internal silent action type
sealed abstract class TauStatus()
case object FnSynch extends TauStatus
case object BnSynch extends TauStatus
case object TestAct extends TauStatus
case object TauAct extends TauStatus

// Iterator type for internal action
class TauIterator(var status: TauStatus,
                  var inputComponent: Int,
                  var inputIndex: Int,
                  var outputComponent: Int,
                  var outputIndex: Int,
                  var testComponent: Int,
                  var testIndex: Int,
                  var tauComponent: Int,
                  var tauIndex: Int)

// Iterator type for label reaction
class LabelIterator(val label: ml.Label,
                    val marker: Array[Boolean],
                    var currentComponent: Int,
                    var currentIndex: Int)

// Iterator type for name reaction
class NameIterator(val alias: String,
                   val actionType: IO,
                   var component: Int,
                   var index: Int)

// Iterator type for kind reaction
class ActionIterator(val actionType: IO,
                     var component: Int,
                     var index: Int)


// Iterator type bundle
sealed abstract class IteratorInfo()
case class TauInfo(tau: TauIterator) extends IteratorInfo
case class LabelInfo(lab: LabelIterator) extends IteratorInfo
case class NameInfo(name: NameIterator) extends IteratorInfo
case class ActionInfo(action: ActionIterator) extends IteratorInfo