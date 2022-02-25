package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import masterproject.GoalBasedProofSystem.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {
  def variable(name: String): Formula = PredicateFormula(SchematicPredicateLabel(name, 0), Seq())

  val (a, b, c) = (variable("a"), variable("b"), variable("c"))

  // ---

  val conclusion: Formula = a ==> (b ==> (a /\ b))
  val steps: IndexedSeq[Tactic] = IndexedSeq(
    TacticAssume(0),
    TacticAssume(0),
    TacticDestructGoal(0),
    TacticWeakenHypothesis(0, 1),
    TacticEliminate(0),
    TacticWeakenHypothesis(0, 0),
    TacticEliminate(0),
  )

  //

  val initialState = formulaToProofState(conclusion)
  println(prettyFrame(prettyProofState(initialState)))
  val finalState = steps.foldLeft(initialState) { (state, tactic) =>
    println()
    println(s"> $tactic")
    tactic(state) match {
      case Some(result) =>
        val newState = mutateState(state, result)
        println()
        println(prettyFrame(prettyProofState(newState)))
        newState
      case None =>
        throw new Exception("Failed to apply this tactic")
    }
  }
  println()
  println("---------------------")
  println()

  if(finalState.goals.nonEmpty) {
    throw new Exception(s"All tactics were applied successfully but the proof is incomplete (${finalState.goals.size} goal(s) remaining)")
  }

  val builder = reconstructProof(conclusion, steps)

  builder.steps.map(s => s"${Printer.prettySequent(s.conclusion)} by ${s.premises.mkString(", ")}").foreach(println)
  println()

  val scproof = builder.build

  println(Printer.prettySCProof(scproof))

  assert(SCProofChecker.checkSCProof(scproof)._1)

  println()
  println("The proof is valid.")
}
