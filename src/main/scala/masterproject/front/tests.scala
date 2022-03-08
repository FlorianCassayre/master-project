package masterproject.front

import masterproject.front.Front.*
import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {

  val (la, lb, lc) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
  val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))

  val initialProofState = ProofState(
    IndexedSeq(
      ProofGoal(
        IndexedSeq(a, b),
        IndexedSeq((b <=> a) /\ (a <=> b))
      )
    )
  )

  val appliedRules: Seq[RuleApplication] = Seq(
    RuleApplication(RuleIntroductionRightAnd),
    RuleApplication(RulePropositionalSolver),
    RuleApplication(RulePropositionalSolver),
  )

  println(initialProofState)
  println()
  println(appliedRules.map(_.rule).mkString("\n\n"))
  println()

  val reconstructed = reconstructSCProof(initialProofState, appliedRules)

  reconstructed match {
    case Some(proof) =>
      println(Printer.prettySCProof(proof))

      println()
      if(proof.imports.nonEmpty) {
        println("Warning, the proof contains imports")
        println()
      }
      if(SCProofChecker.checkSCProof(proof)._1) {
        println("The proof is valid")
      } else {
        println("!!! ERROR !!! The proof is invalid")
      }
    case None =>
      println("Failed to apply a rule and/or reconstruct the proof")
  }

}
