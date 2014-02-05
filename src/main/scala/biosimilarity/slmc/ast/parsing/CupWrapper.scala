package biosimilarity.slmc.ast.parsing

import scala.collection.mutable.HashMap
import scala.collection.JavaConversions
import biosimilarity.slmc.ast.cc
import biosimilarity.slmc.ast.cc._
import biosimilarity.slmc.ast.ml
import biosimilarity.slmc.ast.ml._
import biosimilarity.slmc.ast.pc
import biosimilarity.slmc.ast.pc._
import biosimilarity.slmc.ast.ss
import biosimilarity.slmc.ast.ss._
import biosimilarity.slmc.ast.sr.ParseError

object CW {
  
  //tuple3
  def tuple3[A,B,C](a: A, b: B, c: C): Tuple3[A,B,C] = { (a,b,c) }
  
  // Values
  
  val names: HashMap[String, java.lang.Integer] = new HashMap[String, java.lang.Integer]()
  val usage: HashMap[String, java.lang.Integer] = new HashMap[String, java.lang.Integer]()
  
  def dumpTable(name: String, table: HashMap[String, java.lang.Integer]) {
    println("Dumping " + name + ":")
    for((k,v) <- table) {
      println("  " + k + ": " + v)
    }
  }
  
  // ConversationCalculus
  def ccInaction: ConversationCalculus =
    Inaction

  def ccParallel(ast: ConversationCalculus, ast2: ConversationCalculus): ConversationCalculus =
    cc.Parallel(ast, ast2)

  def ccSum(ast: List[ConversationCalculus]): ConversationCalculus =
    cc.Sum(ast)

  def ccContext(conv: String, ast: ConversationCalculus): ConversationCalculus =
    Context(conv, ast)

  def ccThis(thisVar: String, ast: ConversationCalculus): ConversationCalculus =
    This(thisVar, ast)

  def ccAction(action: cc.ActionType, ast: ConversationCalculus): ConversationCalculus =
    cc.Action(action, ast)

  def ccDefinition(label: String, ast: ConversationCalculus): ConversationCalculus =
    Definition(label, ast)

  def ccNew(conv: String, label: String, ast: ConversationCalculus): ConversationCalculus =
    cc.New(conv, label, ast)

  def ccJoin(conv: String, label: String, ast: ConversationCalculus): ConversationCalculus =
    Join(conv, label, ast)

  def ccVariable(name: String, arguments: List[String]): ConversationCalculus =
    cc.Variable(name, arguments)

  def ccIfThenElse(astt: ConversationCalculus, astf: ConversationCalculus): ConversationCalculus =
    IfThenElse(astt, astf)
    
  def ccHere(): Direction = 
    Here
    
  def ccUp(): Direction = 
    Up

  def ccInput(direction: Direction, label: String, args: List[String]): cc.ActionType =
    cc.Input(direction, label, args)
    
  def ccOutput(direction: Direction, label: String, args: List[String]): cc.ActionType =
    cc.Output(direction, label, args)
    
  // PiCalculus
  def pcVoid : PiCalculus =
    pc.Void
    
  def pcParallel(left: PiCalculus, right: PiCalculus) : PiCalculus =
    pc.Parallel(left, right)

  def pcSum(left: PiCalculus, right: PiCalculus) : PiCalculus =
    pc.Sum(left, right)
    
  def pcNew(names: List[String], process: PiCalculus) : PiCalculus =
    pc.New(names, process)

  def pcAction(action: pc.ActionType, next: PiCalculus) : PiCalculus =
    pc.Action(action, next)
    
  def pcTest(left: String, right: String, process: PiCalculus, test: TestType) : PiCalculus =
    Test(left, right, process, test)

  def pcVariable(name: String, arguments: List[String]) : PiCalculus =
    pc.Variable(name, arguments)

  
  def pcInput(channel: String, arguments: List[String]): pc.ActionType =
    pc.Input(channel, arguments)
    
  def pcOutput(channel: String, arguments: List[String]): pc.ActionType =
    pc.Output(channel, arguments)
    
  def pcTau(): pc.ActionType = 
    pc.Tau
    
  def pcEquals(): pc.TestType =
    Equals
    
  def pcDiffers(): pc.TestType =
    Differs
    
  // ModalLogic
  def mlTrue: ModalLogic =
    ml.True

  def mlFalse: ModalLogic =
    ml.False

  def mlVoid: ModalLogic =
    ml.Void

  def mlCompare(i: Integer, t: ComparisonType): ModalLogic =
    Compare(i, t)

  def mlEqual(id1: String, id2: String): ModalLogic =
    Equal(id1, id2)

  def mlNotEqual(id1: String, id2: String): ModalLogic =
    NotEqual(id1, id2)

  def mlCompose(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    Compose(f1, f2)

  def mlDecompose(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    Decompose(f1, f2)

  def mlNot(f: ModalLogic): ModalLogic =
    Not(f)

  def mlAnd(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    And(f1, f2)

  def mlOr(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    Or(f1, f2)

  def mlImplies(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    Implies(f1, f2)

  def mlEquivalent(f1: ModalLogic, f2: ModalLogic): ModalLogic =
    Equivalent(f1, f2)

  def mlReveal(s: String, f: ModalLogic): ModalLogic =
    Reveal(s, f)

  def mlRevealAll(s: String, f: ModalLogic): ModalLogic =
    RevealAll(s, f)

  def mlFresh(s: String, f: ModalLogic): ModalLogic =
    Fresh(s, f)

  def mlFree(s: String): ModalLogic =
    Free(s)

  def mlHidden(s: String, f: ModalLogic): ModalLogic =
    Hidden(s, f)

  def mlMayTau(f: ModalLogic): ModalLogic =
    MayTau(f)

  def mlAllTau(f: ModalLogic): ModalLogic =
    AllTau(f)

  def mlMayLabelled(l: Label, f: ModalLogic): ModalLogic =
    MayLabelled(l, f)

  def mlAllLabelled(l: Label, f: ModalLogic): ModalLogic =
    AllLabelled(l, f)

  def mlMayOutputN(s: String, f: ModalLogic): ModalLogic =
    MayOutputN(s, f)

  def mlMayInputN(s: String, f: ModalLogic): ModalLogic =
    MayInputN(s, f)

  def mlAllOutputN(s: String, f: ModalLogic): ModalLogic =
    AllOutputN(s, f)

  def mlAllInputN(s: String, f: ModalLogic): ModalLogic =
    AllInputN(s, f)

  def mlMayOutput(f: ModalLogic): ModalLogic =
    MayOutput(f)

  def mlMayInput(f: ModalLogic): ModalLogic =
    MayInput(f)

  def mlAllOutput(f: ModalLogic): ModalLogic =
    AllOutput(f)

  def mlAllInput(f: ModalLogic): ModalLogic =
    AllInput(f)

  def mlMayN(s: String, f: ModalLogic): ModalLogic =
    MayN(s, f)

  def mlAllN(s: String, f: ModalLogic): ModalLogic =
    AllN(s, f)

  def mlMay(f: ModalLogic): ModalLogic =
    May(f)

  def mlAll(f: ModalLogic): ModalLogic =
    All(f)

  def mlExists(s: String, f: ModalLogic): ModalLogic =
    Exists(s, f)

  def mlForAll(s: String, f: ModalLogic): ModalLogic =
    ForAll(s, f)

  def mlMaximumFixpoint(variable: String, parameters: List[String], formula: ModalLogic, arguments: List[String]): ModalLogic =
    MaximumFixpoint(variable, parameters, formula, arguments)

  def mlMinimumFixpoint(variable: String, parameters: List[String], formula: ModalLogic, arguments: List[String]): ModalLogic =
    MinimumFixpoint(variable, parameters, formula, arguments)

  def mlEventually(f: ModalLogic): ModalLogic =
    Eventually(f)

  def mlAlways(f: ModalLogic): ModalLogic =
    Always(f)

  def mlInside(f: ModalLogic): ModalLogic =
    Inside(f)

  def mlShowFails(f: ModalLogic): ModalLogic =
    ShowFails(f)

  def mlShowSucceeds(f: ModalLogic): ModalLogic =
    ShowSucceeds(f)

  def mlPropositionVariable(s: String, sl: List[String]): ModalLogic =
    PropositionVariable(s, sl)

  def mlAbbreviate(s: String, fs: List[ModalLogic]): ModalLogic =
    Abbreviate(s, fs)

  def mlOutLab(name: String, arguments: List[String]): Label =
    ml.Output(name, arguments)

  def mlInpLab(name: String, arguments: List[String]): Label =
    ml.Input(name, arguments)
    
  def mlEqNum(): ComparisonType =
    EqNum
    
  def mlGtNum(): ComparisonType =
    GtNum
  
  def mlLtNum(): ComparisonType =
    LtNum
    
  //SLMC Statements
  def ssClear: SLMCStatement =
    Clear

  def ssDone: SLMCStatement =
    Done

  def ssHelp: SLMCStatement =
    Help

  def ssListParameters: SLMCStatement =
    ListParameters
    
  def ssPass: SLMCStatement =
    Pass

  def ssPrintCheckCounter: SLMCStatement =
    PrintCheckCounter

  def ssPrintDirectory: SLMCStatement =
    PrintDirectory

  def ssPrintMaxThreads: SLMCStatement =
    PrintMaxThreads

  def ssPrintProcesses: SLMCStatement =
    PrintProcesses

  def ssPrintPropositions: SLMCStatement =
    PrintPropositions

  def ssPrintShowTime: SLMCStatement =
    PrintShowTime

  def ssPrintTrace: SLMCStatement =
    PrintTrace

  def ssCheck(name: String, arguments: List[String], proposition: ModalLogic): SLMCStatement =
    Check(name, arguments, proposition)

  def ssDefineMaxThreads(max: Integer): SLMCStatement =
    DefineMaxThreads(max)

  def ssDefinePiProcesses(names: List[String], argumentss: List[List[String]], definitions: List[PiCalculus]): SLMCStatement =
    DefinePiProcesses(names, argumentss, definitions)

  def ssDefineCCProcess(name: String, arguments: List[String], definition: ConversationCalculus): SLMCStatement =
    DefineCCProcess(name, arguments, definition)

  def ssDefineProposition(name: String, parameters: List[String], propositions: List[String], definition: ModalLogic): SLMCStatement =
    DefineProposition(name, parameters, propositions, definition)

  def ssDefineCheckCounter(check: java.lang.Boolean): SLMCStatement =
    DefineCheckCounter(check)

  def ssDefineShowTime(showTime: java.lang.Boolean): SLMCStatement =
    DefineShowTime(showTime)

  def ssDefineTrace(trace: java.lang.Boolean): SLMCStatement =
    DefineTrace(trace)

  def ssChangeDirectory(directory: String): SLMCStatement =
    ChangeDirectory(directory)

  def ssLoad(file: String): SLMCStatement =
    Load(file)

  def ssShowProcess(process: String): SLMCStatement =
    ShowProcess(process)

  def ssShowProposition(proposition: String): SLMCStatement =
    ShowProposition(proposition)
  
  // Helpers
  
  def makeIterable[A](l: List[A]) = {
    JavaConversions.asJavaIterable(l)
  }
  def error() {
  	throw new ParseError("");
  }
  
  def error(msg: String = "") {
  	throw new ParseError(msg);
  }
  

}