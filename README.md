#AST#

The `ast` package is broken into five sub-packages:

1.  Pi Calculus           - Core language for process descriptions

2.  Modal Logic           - Core language for process specifications

3.  SLMC Statements       - Top level language for populating the SLMC environment

4.  SLMC Responses        - Enumeration of responses to SLMC Statements

5.  Conversation Calculus - Alternative to the Pi Calculus.  Compiled back into Pi Calculus at runtime.

The packages are named `pc`, `ml`, `ss`, `sr`, and `cc` respectively.

Due to name collisions, it is recommended to import each package with it's qualifying name

##Data Types##

Following are the AST abstract/case classes (in some kind of mongrel shorthand)

###Pi Calculus###

```
type PiCalculus
 = Void
 | Parallel(PiCalculus, PiCalculus)
 | Sum(PiCalculus, PiCalculus)
 | New(List[String], PiCalculus)
 | Action(ActionType, PiCalculus)
 | Test(String, String, PiCalculus, TestType)
 | Variable(String, List[String])
 
and ActionType
 = Input(String, List[String])
 | Output(String, List[String])
 
and TestType = Equals | Differs
```

###Modal Logic###

```
type ModalLogic
 = True 
 | False 
 | Void 
 | Compare(Integer, ComparisonType) 
 | Equal(String, String) 
 | NotEqual(String, String) 
 | Compose(ModalLogic, ModalLogic) 
 | Decompose(ModalLogic, ModalLogic) 
 | Not(ModalLogic) 
 | And(ModalLogic, ModalLogic) 
 | Or(ModalLogic, ModalLogic) 
 | Implies(ModalLogic, ModalLogic) 
 | Equivalent(ModalLogic, ModalLogic) 
 | Reveal(String, ModalLogic) 
 | RevealAll(String, ModalLogic) 
 | Fresh(String, ModalLogic) 
 | Free(String) 
 | Hidden(String, ModalLogic) 
 | MayTau(ModalLogic) 
 | AllTau(ModalLogic) 
 | MayLabelled(Label, ModalLogic) 
 | AllLabelled(Label, ModalLogic) 
 | MayOutputN(String, ModalLogic) 
 | MayInputN(String, ModalLogic) 
 | AllOutputN(String, ModalLogic) 
 | AllInputN(String, ModalLogic) 
 | MayOutput(ModalLogic) 
 | MayInput(ModalLogic) 
 | AllOutput(ModalLogic) 
 | AllInput(ModalLogic) 
 | MayN(String, ModalLogic) 
 | AllN(String, ModalLogic) 
 | May(ModalLogic) 
 | All(ModalLogic) 
 | Exists(String, ModalLogic) 
 | ForAll(String, ModalLogic) 
 | MaximumFixpoint(String, List[String], ModalLogic, List[String]) 
 | MinimumFixpoint(String, List[String], ModalLogic, List[String]) 
 | Eventually(ModalLogic) 
 | Always(ModalLogic) 
 | Inside(ModalLogic) 
 | ShowFails(ModalLogic) 
 | ShowSucceeds(ModalLogic) 
 | PropositionVariable(String, List[String]) 
 | Abbreviate(String, List[ModalLogic])
 
and Label
 = Output(String, List[String])
 | Input(String, List[String])
 
and ComparisonType = EqNum | GtNum | LtNum
```

###SLMC Statement###

```
type SLMCStatement
 = Pass
 | Help
 | ListParameters
 | Clear
 | PrintProcesses
 | ShowProcess(String)
 | DefineCCProcess(String, List[String], ConversationCalculus)
 | DefinePiProcesses(List[String], List[List[String]], List[PiCalculus])
 | PrintPropositions
 | ShowProposition(String)
 | DefineProposition(String, List[String], List[String], ModalLogic)
 | Check(String, List[String], ModalLogic)
 | PrintCheckCounter
 | DefineCheckCounter(Boolean)
 | PrintDirectory
 | ChangeDirectory(String)
 | PrintMaxThreads
 | DefineMaxThreads(Integer)
 | PrintPropositions
 | PrintShowTime
 | DefineShowTime(Boolean)
 | PrintTrace
 | DefineTrace(Boolean)
 | Done
```

###SLMC Response###

```
type SLMCResponse
 = Fail(String)
 | ParseError(String)
 | IllFormedAst(String)
 | UnguardedRecursion(String)
 | MaxThreads(String)
 | UndeclaredIdentifier(String)
 | WrongArguments(String)
 | WrongArgumentCount(String)
 | OK(String)
 | CheckComplete(Boolean, String)
```

###Conversation Calculus###

```
type ConversationCalculus
 = Inaction
 | Parallel(ConversationCalculus, ConversationCalculus)
 | Sum(List[ConversationCalculus])
 | Context(String, ConversationCalculus)
 | This(String, ConversationCalculus)
 | Action(ActionType, ConversationCalculus)
 | Definition(String, ConversationCalculus)
 | New(String, String, ConversationCalculus)
 | Join(String, String, ConversationCalculus)
 | Variable(String, List[String])
 | IfThenElse(ConversationCalculus, ConversationCalculus)
 
and ActionType
 = Input(Direction, String, List[String])
 | Output(Direction, String, List[String])
 
and Direction = Here | Up
```

#Class Summary#

##The Important Ones##

###SLMC###

```
SLMC
 - installConversationCalculus: (String, List[String], ConversationCalculus) => SLMC 
 - installPiProcesses: (List[String], List[List[String]], List[PiCalculus]) => SLMC
 - installProposition: (String, List[String], ModalLogic) => SLMC
 - showProcess: String => String
 - showProcesses: String
 - showProposition: String => String
 - showPropositions: String
```

`SLMC` represents the environment in which SLMC programs are evaluated.
It is immutable; Each destructive command returns a new SLMC environment.
SLMC is passed as an argument to Checker, along with the process name being checked.


###Evaluator###

```
Evaluator
 - apply: (SLMC, SLMCStatement) => (SLMC, SLMCResponse)
```

Evaluator encapsulates the function responsible for executing SLMC statements.
It takes as arguments, an SLMC environment and and SLMC statement, returning a new environment and response as it's result.

###Checker###

```
Checker
 - checkCounter: Int
 - maxThreads: Int
 - showCheckCounter: Boolean
 - showTime: Boolean
 - showTrace: Boolean
 - timeout: Duration
 - check: (SLMC, String, List[String], ModalLogic) => (Boolean, String)
```

`checkCounter` increments each time `check` is called, by the user or by sub-calls from `check` itself.

`maxThreads` is an arbitrary cap on the parallel size of a process being checked, doesn't reflect any true application parallelism, is set arbitrarily high and should be removed.

`showCheckCounter` determines if checkCounter is printed during evaluation.

`showTime` determines if the duration of the check should be printed after the check completes.

`showTrace` determines if extra details of the check should be printed during the check.

`timeout` determines how long Checker should try to solve a given assertion before failing with CheckerTimedOut.

`check` takes as its arguments an SLMC environment, the name of a process in that environment, the process arguments, and the Modal Logic proposition the process should check against.

It returns true if the process satisfies the proposition, as well as a response string to print to the console.

###SLMCScript###

```
SLMCScript
 - SLMCScript: String => SLMCScript
 - evaluate: SLMC => (SLMC, String)
 - save: String => Unit
 - show: Unit => String

 - fromString: Unit => SLMCScript
```

The constructor loads a script from a given filename

`evaluate` takes a (possibly prepared) SLMC environment and returns an updated environment and the aggregated responses.

`save` saves this script to a file.

`show` returns a string representation of this file

`fromString` is static, taking a sequence of strings as a command and returning a new SLMCScript.

SLMCScript extends SeqProxy[SLMCStatement], and so inherits all of the useful Seq functions (such as `++` and `filter`)

##Other Classes##

###Parser###

```
Parser
 - hasNext: Boolean
 - next: SLMCStatement

 - fromStdin: Unit => Parser
 - fromFile: String => Parser
 - fromInputStream: InputStream => Parser
 - fromString: String => Parser
```

Parser extends Iterator[SLMCStatement], so it can be used in for-comprehensions.

Parsers can be built from stdin, files, input streams, and strings, by using the appropriate factory methods.

#Usage#

##Requirements##
* Maven
* Scala

##Launching the Toplevel##

```
> mvn package
> mvn scala:console
```



* Document in progress as of 12:35PM, 11/11/2013 *
