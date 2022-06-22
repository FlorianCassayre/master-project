package me.cassayre.florian.masterproject.legacy

import me.cassayre.florian.masterproject.legacy.parser.SCReader
import me.cassayre.florian.masterproject.legacy.GoalBasedProofSystem.*

import java.util.Scanner
import scala.util.{Failure, Success, Try}
import lisa.kernel.fol.FOL.*
import utilities.Printer
import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.settheory.AxiomaticSetTheory

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

  val availableTactics: Map[String, PartialFunction[Seq[Matchable], Tactic]] = Map(
    "assume" -> { case Seq() => TacticAssume },
    "weaken_hypothesis" -> { case Seq(hypothesisIndex: Int) => TacticWeakenHypothesis(hypothesisIndex) },
    "eliminate" -> { case Seq() => TacticEliminate },
    "destruct_hypothesis" -> { case Seq(hypothesisIndex: Int) => TacticDestructHypothesis(hypothesisIndex) },
    "destruct_goal" -> { case Seq() => TacticDestructGoal },
    "or_hypothesis" -> { case Seq(hypothesisIndex: Int) => TacticOrHypothesis(hypothesisIndex) },
    "or_n_goal" -> { case Seq(n: Int) => TacticOrNGoal(n) },
    "solver" -> { case Seq() => TacticPropositionalSolver },
    "instantiate" -> { case Seq() => TacticInstantiateForall },
    "axiom" -> { case Seq() => TacticAxiom },
    "reorder" -> { case Seq(goalIndex: Int) => TacticReorder(goalIndex) },
    "cut" -> { case Seq(formula: Formula) => TacticCut(formula) },
    "transitivity" -> { case Seq(hypothesisIndex: Int) => TacticTransitivity(hypothesisIndex) }
  )

  sealed abstract class REPLState
  case class StateInitial(theory: RunningTheory) extends REPLState
  case class StateTactical(
                            formula: Formula,
                            proofState: ProofState,
                            tacticsUsed: IndexedSeq[Tactic],
                            history: Seq[(ProofState, IndexedSeq[Tactic])],
                            theory: RunningTheory,
                          ) extends REPLState

  case class REPLOutput(private val strings: Seq[String] = Seq.empty) {
    def println(line: String = ""): REPLOutput = copy(strings = "\n" +: line +: strings)
    def print(string: String): REPLOutput = copy(strings = string +: strings)
    def build: String = strings.reverse.mkString
  }

  def stateOutput(state: REPLState): REPLOutput = state match {
    case StateInitial(_) =>
      REPLOutput()
        .print("Enter the formula you would like to prove: ")
    case StateTactical(_, proofState, _, _, _) =>
      REPLOutput()
        .println()
        .println(prettyFrame(prettyProofState(proofState)))
        .println()
        .print("Select a tactic to apply (or < to undo the previous step): ")
  }

  def stateReducer(state: REPLState, input: String): (REPLState, REPLOutput) = state match {
    case StateInitial(theory) =>
      Try {
        SCReader.readFormulaAscii(input)
      } match {
        case Success(formula) =>
          (StateTactical(formula, formulaToProofState(formula), IndexedSeq.empty, Seq.empty, theory),
            REPLOutput().print(""))
        case Failure(exception) =>
          (state, REPLOutput()
            .println("The string you entered couldn't be parsed (see the stack trace below), please try again.")
            .println(stacktraceToString(exception))
            .println())
      }
    case state @ StateTactical(formula, proofState, tacticsUsed, history, theory) =>
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
        val parts = input.split("\\s+", 2).toIndexedSeq
        val tacticName = parts.head
        val remaining = parts.tail.mkString
        val argsOpt: Option[Seq[Matchable]] =
          if(remaining.trim.isEmpty) {
            Some(Seq.empty)
          } else if(remaining.forall(_.isDigit)) {
            Some(Seq(remaining.toInt))
          } else {
            Try(SCReader.readFormulaAscii(remaining)).toOption.map(Seq(_))
          }
        argsOpt match {
          case Some(args) =>
            availableTactics.get(tacticName) match {
              case Some(f) =>
                f.unapply(args) match {
                  case Some(tactic) =>
                    val output = REPLOutput().println().println(s"> $tactic")

                    tactic(proofState, theory) match {
                      case Some(result) =>
                        val newState = state.copy(proofState = mutateState(proofState, result), tacticsUsed = tacticsUsed :+ tactic, history = (proofState, tacticsUsed) +: history)

                        if(newState.proofState.goals.nonEmpty) {
                          (newState, output)
                        } else {
                          val proof = reconstructProof(formula, newState.tacticsUsed, theory).build
                          val judgement = SCProofChecker.checkSCProof(proof)

                          (StateInitial(theory), REPLOutput()
                            .println()
                            .println(prettyFrame(prettyProofState(newState.proofState)))
                            .println()
                            .println("All goals have been proven, the proof will now be reconstructed below:")
                            .println(Printer.prettySCProof(judgement))
                            .println()
                            .println(
                              if(judgement.isValid)
                                "This proof was successfully verified by the kernel."
                              else
                                "!!! ERROR !!! The reconstructed proof is invalid!\nThis may indicate an issue with a tactic."
                            )
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
          case None =>
            (state, REPLOutput().println("Invalid tactic arguments format, please try again."))
        }
      }
  }

  @main def repl(): Unit = {
    val scanner = new Scanner(System.in)
    var state: REPLState = StateInitial(AxiomaticSetTheory.runningSetTheory)
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
