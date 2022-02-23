package masterproject

//import lisa.kernel.proof.RunningTheory.Axiom
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.Sequent
//import lisa.settheory.AxiomaticSetTheory.Axiom
//import lisa.KernelHelpers.*
import masterproject.SCProofBuilder.SCAnyProofStep

object SCProofBuilder {

  case class SCAnyProofStep(conclusion: Sequent, premises: Seq[Int], imports: Seq[Sequent])

  implicit class SequentBy(s: Sequent) {
    def by(premises: Int*): SCAnyProofStep = SCAnyProofStep(s, premises, Seq.empty)
    def justifiedBy(sequents: Sequent*): SCAnyProofStep = SCAnyProofStep(s, Seq.empty, sequents)
    //def justifiedBy(axiom: Axiom): SCAnyProofStep = SCAnyProofStep(s, Seq.empty, Seq(() |- axiom))
  }
  implicit def sequentToCoreProofStep(s: Sequent): SCAnyProofStep = SCAnyProofStep(s, Seq.empty, Seq.empty)

  def apply(steps: SCAnyProofStep*): SCProofBuilder = new SCProofBuilder(steps.toIndexedSeq)

}

case class SCProofBuilder(steps: IndexedSeq[SCAnyProofStep]) {
  def build: SCProof = {
    // (proof, indices mapping, imports mapping)
    val (proof, _, _) = steps.zipWithIndex.foldLeft((SCProof.apply(), Map.empty[Int, Int], Map.empty[Sequent, Int])) { case ((proof, stepsMapping, importsMapping), (SCAnyProofStep(conclusion, premises, imports), i)) =>
      val newImports = imports.foldLeft(importsMapping)((currentImports: Map[Sequent, Int], toImport: Sequent) => if(currentImports.contains(toImport)) currentImports else currentImports + (toImport -> currentImports.size))
      val usedImports = imports.map(imp => -(newImports(imp) + 1))
      val newProof = SCProofStepFinder.proofStepFinder(proof.copy(imports = newImports.toIndexedSeq.sortBy(_._2).map(_._1)), conclusion, premises ++ usedImports)
      val newMapping = stepsMapping + (i -> (newProof.steps.size - 1))
      (newProof, newMapping, newImports)
    }
    proof
  }
}
