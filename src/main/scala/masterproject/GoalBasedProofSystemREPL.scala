package masterproject

import masterproject.parser.{SCAsciiParser, SCResolver}
import masterproject.GoalBasedProofSystem.*

import java.util.Scanner
import scala.util.{Failure, Success, Try}
import lisa.kernel.fol.FOL.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

object GoalBasedProofSystemREPL {

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

  @main def repl(): Unit = {
    val scanner = new Scanner(System.in)

    while(true) {
      var formula: Formula = null
      while(formula == null) {
        print("Enter the formula you would like to prove: ")
        val input = scanner.nextLine()
        Try {
          SCResolver.resolveTopLevelFormula(SCAsciiParser.parseTermOrFormula(input))
        } match {
          case Success(value) =>
            println()
            formula = value
          case Failure(exception) =>
            println("The string you entered couldn't be parsed (see the stack trace below), please try again.")
            exception.printStackTrace()
            println()
        }
      }

      var state: ProofState = formulaToProofState(formula)
      var tacticsUsed: IndexedSeq[Tactic] = IndexedSeq.empty

      var history: Seq[(ProofState, IndexedSeq[Tactic])] = Seq.empty

      while(state.goals.nonEmpty) {
        println(prettyFrame(prettyProofState(state)))
        println()
        var tactic: Tactic = null
        while(tactic == null) {
          print("Select a tactic to apply (or < to undo the previous step): ")
          val input = scanner.nextLine()
          if(input.trim == "<") {
            history match {
              case (newState, newTacticsUsed) +: tail =>
                state = newState
                tacticsUsed = newTacticsUsed
                history = tail
                println("Undid one tactic.")
                println()
                println(prettyFrame(prettyProofState(state)))
                println()
              case _ =>
                println("Cannot undo, this is already the first step.")
            }
          } else {
            val parts = input.split("\\s+").toIndexedSeq
            val tacticName = parts.head
            if(parts.tail.forall(_.forall(_.isDigit))) {
              val arguments = parts.tail.map(_.toInt)
              availableTactics.get(tacticName) match {
                case Some(f) =>
                  f.unapply(arguments) match {
                    case Some(result) => tactic = result
                    case None =>
                      println(s"Incorrect number of arguments for tactic $tacticName, please try again.")
                  }
                case None =>
                  println("No registered tactic with this name, please try again.")
              }
            } else {
              println("Invalid tactic arguments format, please try again.")
            }
          }
        }

        println()
        println(s"> $tactic")
        println()

        tactic(state) match {
          case Some(result) =>
            history = (state, tacticsUsed) +: history
            state = mutateState(state, result)
            tacticsUsed = tacticsUsed :+ tactic
          case None =>
            println("This tactic failed to apply in this context, please try again.")
            println()
        }
      }
      println(prettyFrame(prettyProofState(state)))
      println()
      println("All goals have been proven, the proof will now be reconstructed below:")

      val proof = reconstructProof(formula, tacticsUsed).build
      println(Printer.prettySCProof(proof))

      assert(SCProofChecker.checkSCProof(proof)._1)

      println()
      println("This proof was successfully verified by the kernel.")

      println("--------")
      println()

    }
  }

}
