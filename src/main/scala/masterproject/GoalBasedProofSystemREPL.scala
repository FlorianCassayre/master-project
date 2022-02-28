package masterproject

import masterproject.parser.{SCAsciiParser, SCResolver}
import masterproject.GoalBasedProofSystem.*

import java.util.Scanner
import scala.util.{Failure, Success, Try}
import lisa.kernel.fol.FOL.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

object GoalBasedProofSystemREPL {

  private def stacktraceToString(e: Throwable): String = {
    import java.io.PrintWriter
    import java.io.StringWriter
    val sw = new StringWriter
    val pw = new PrintWriter(sw)
    e.printStackTrace(pw)
    val string = sw.toString
    pw.close()
    string
  }

  val availableTactics: Map[String, PartialFunction[Seq[Int], Tactic]] = Map(
    "assume" -> { case Seq(goalIndex) => TacticAssume(goalIndex) },
    "weaken_hypothesis" -> { case Seq(goalIndex, hypothesisIndex) => TacticWeakenHypothesis(goalIndex, hypothesisIndex) },
    "eliminate" -> { case Seq(goalIndex) => TacticEliminate(goalIndex) },
    "destruct_hypothesis" -> { case Seq(goalIndex, hypothesisIndex) => TacticDestructHypothesis(goalIndex, hypothesisIndex) },
    "destruct_goal" -> { case Seq(goalIndex) => TacticDestructGoal(goalIndex) },
    "or_hypothesis" -> { case Seq(goalIndex, hypothesisIndex) => TacticOrHypothesis(goalIndex, hypothesisIndex) },
    "or_n_goal" -> { case Seq(goalIndex, n) => TacticOrNGoal(goalIndex, n) },
    "solver" -> { case Seq(goalIndex) => TacticPropositionalSolver(goalIndex) },
  )

  sealed abstract class REPLState
  case object StateInitial extends REPLState
  case class StateTactical(
                            formula: Formula,
                            proofState: ProofState,
                            tacticsUsed: IndexedSeq[Tactic],
                            history: Seq[(ProofState, IndexedSeq[Tactic])]
                          ) extends REPLState

  case class REPLOutput(private val strings: Seq[String] = Seq.empty) {
    def println(line: String = ""): REPLOutput = copy(strings = "\n" +: line +: strings)
    def print(string: String): REPLOutput = copy(strings = string +: strings)
    def build: String = strings.reverse.mkString
  }

  def stateOutput(state: REPLState): REPLOutput = state match {
    case StateInitial =>
      REPLOutput()
        .print("Enter the formula you would like to prove: ")
    case StateTactical(formula, proofState, tacticsUsed, history) =>
      REPLOutput()
        .println()
        .println(prettyFrame(prettyProofState(proofState)))
        .println()
        .print("Select a tactic to apply (or < to undo the previous step): ")
  }

  def stateReducer(state: REPLState, input: String): (REPLState, REPLOutput) = state match {
    case StateInitial =>
      Try {
        SCResolver.resolveTopLevelFormula(SCAsciiParser.parseTermOrFormula(input))
      } match {
        case Success(formula) =>
          (StateTactical(formula, formulaToProofState(formula), IndexedSeq.empty, Seq.empty),
            REPLOutput().print(""))
        case Failure(exception) =>
          (state, REPLOutput()
            .println("The string you entered couldn't be parsed (see the stack trace below), please try again.")
            .println(stacktraceToString(exception))
            .println())
      }
    case state @ StateTactical(formula, proofState, tacticsUsed, history) =>
      if(input.trim == "<") {
        history match {
          case (newProofState, newTacticsUsed) +: tail =>
            (state.copy(proofState = newProofState, tacticsUsed = newTacticsUsed, history = tail),
              REPLOutput()
                .println("Undid one tactic.").println().println(prettyFrame(prettyProofState(proofState))).println())
          case _ =>
            (state, REPLOutput().println("Cannot undo, this is already the first step."))
        }
      } else {
        val parts = input.split("\\s+").toIndexedSeq
        val tacticName = parts.head
        if(parts.tail.forall(_.forall(_.isDigit))) {
          val arguments = parts.tail.map(_.toInt)
          availableTactics.get(tacticName) match {
            case Some(f) =>
              f.unapply(arguments) match {
                case Some(tactic) =>
                  val output = REPLOutput().println().println(s"> $tactic")

                  tactic(proofState) match {
                    case Some(result) =>
                      val newState = state.copy(proofState = mutateState(proofState, result), tacticsUsed = tacticsUsed :+ tactic, history = (proofState, tacticsUsed) +: history)

                      if(newState.proofState.goals.nonEmpty) {
                        (newState, output)
                      } else {
                        val proof = reconstructProof(formula, newState.tacticsUsed).build
                        assert(SCProofChecker.checkSCProof(proof)._1)

                        (StateInitial, REPLOutput()
                          .println()
                          .println(prettyFrame(prettyProofState(newState.proofState)))
                          .println()
                          .println("All goals have been proven, the proof will now be reconstructed below:")
                          .println(Printer.prettySCProof(proof))
                          .println()
                          .println("This proof was successfully verified by the kernel.")
                          .println()
                          .println("--------")
                          .println())
                      }
                    case None =>
                      (state, output.println("This tactic failed to apply in this context, please try again."))
                  }
                case None =>
                  (state, REPLOutput().println(s"Incorrect number of arguments for tactic $tacticName, please try again."))
              }
            case None =>
              (state, REPLOutput().println("No registered tactic with this name, please try again."))
          }
        } else {
          (state, REPLOutput().println("Invalid tactic arguments format, please try again."))
        }
      }
  }

  @main def repl(): Unit = {
    val scanner = new Scanner(System.in)
    var state: REPLState = StateInitial
    while(true) {
      val output1 = stateOutput(state)
      print(output1.build)
      val input = scanner.nextLine()
      val (newState, output2) = stateReducer(state, input)
      state = newState
      print(output2.build)
    }
  }

}
