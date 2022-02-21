package masterproject

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
import masterproject.SCProofBuilder.SCAnyProofStep

object SCProofBuilder {

  case class SCAnyProofStep(conclusion: Sequent, premises: Seq[Int])

  implicit class SequentBy(s: Sequent) {
    def by(premises: Int*): SCAnyProofStep = SCAnyProofStep(s, premises)
  }
  implicit def sequentTooCoreProofStep(s: Sequent): SCAnyProofStep = SCAnyProofStep(s, Seq.empty)

  def apply(steps: SCAnyProofStep*): SCProofBuilder = new SCProofBuilder(steps.toIndexedSeq)

}

case class SCProofBuilder(steps: IndexedSeq[SCAnyProofStep]) {
  def build: SCProof = {
    val (proof, _) = steps.zipWithIndex.foldLeft((SCProof.apply(), Map.empty[Int, Int])) { case ((proof, mapping), (SCAnyProofStep(conclusion, premises), i)) =>
      val newProof = ProofStepFinder.proofStepFinder(proof, conclusion, premises)
      val newMapping = mapping + (i -> (newProof.steps.size - 1))
      (newProof, newMapping)
    }
    proof
  }
}
