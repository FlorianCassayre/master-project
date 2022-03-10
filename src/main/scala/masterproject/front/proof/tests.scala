package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {

  val (la, lb, lc) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))
  val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))

  val initialProofState = ProofState(
    IndexedSeq(
      Sequent(
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
