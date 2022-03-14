package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.proof.{RunningTheory, SCProofChecker}
import lisa.settheory.AxiomaticSetTheory
import masterproject.GoalBasedProofSystem.*
import org.scalatest.funsuite.AnyFunSuite

class GoalBasedProofSystemTests extends AnyFunSuite {

  def checkGoalProof(statement: Formula)(tactics: Tactic*): Unit = {
    val theory: RunningTheory = AxiomaticSetTheory.runningSetTheory
    val finalState = tactics.zipWithIndex.foldLeft(formulaToProofState(statement)) { case (state, (tactic, i)) =>
      tactic(state, theory) match {
        case Some(result) =>
          mutateState(state, result)
        case None =>
          throw new Exception(s"Failed to apply tactic #$i: $tactic")
      }
    }

    assert(finalState.goals.isEmpty, s"There are ${finalState.goals.size} goal(s) remaining to be proven\n\n${prettyProofState(finalState)}\n")

    val hlproof = reconstructProof(statement, tactics, theory)
    val proof = hlproof.build

    assert(proof.conclusion == (() |- statement), s"The conclusion of the reconstruct proof does not match the statement that was to be proven")

    val judgement = SCProofChecker.checkSCProof(proof)

    // For some output
    println(Printer.prettySCProof(proof, judgement))
    println()

    assert(judgement.isValid, "The validity of the reconstructed proof couldn't be certified")
  }

  test("goal based proof system") {
    val (la, lb, lc) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
    val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))

    checkGoalProof(a ==> a)(
      TacticAssume,
      TacticEliminate,
    )

    checkGoalProof(((a ==> b) /\ (b ==> a)) <=> (a <=> b))(
      TacticDestructGoal,
      TacticAssume,
      TacticDestructGoal,
      TacticDestructHypothesis(0),
      TacticReorder(1),
      TacticDestructHypothesis(0),
      TacticEliminate,
      TacticEliminate,
      TacticPropositionalSolver,
    )

    checkGoalProof(a \/ !a)(TacticPropositionalSolver)
  }

}
