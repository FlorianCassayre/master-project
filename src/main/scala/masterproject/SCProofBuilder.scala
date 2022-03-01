package masterproject

import lisa.kernel.proof.{SCProof, SequentCalculus}
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.Axiom

object SCProofBuilder {

  sealed abstract class SCHighLevelProofStep

  case class SCImplicitProofStep(conclusion: Sequent, premises: Seq[Int] = Seq.empty, imports: Seq[Sequent] = Seq.empty) extends SCHighLevelProofStep
  case class SCExplicitProofStep(step: SCProofStep) extends SCHighLevelProofStep

  implicit class SequentBy(s: Sequent) {
    def by(premises: Int*): SCImplicitProofStep = SCImplicitProofStep(s, premises, Seq.empty)
    def by(step: SCProofStep): SCExplicitProofStep = SCExplicitProofStep(step)
    def justifiedBy(sequents: Sequent*): SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, sequents)
    def justifiedBy(axiom: Axiom): SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, Seq(Sequent(Set.empty, Set(axiom))))
    def justified: SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, Seq(s))
  }
  implicit def sequentToCoreProofStep(s: Sequent): SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, Seq.empty)

  def apply(steps: SCHighLevelProofStep*): SCProofBuilder = new SCProofBuilder(steps.toIndexedSeq)

}

import masterproject.SCProofBuilder.*

case class SCProofBuilder(steps: IndexedSeq[SCHighLevelProofStep]) {

  def build: SCProof = {
    // (proof, indices mapping, imports mapping)
    val (proof, _, _) = steps.zipWithIndex.foldLeft((SCProof.apply(), Map.empty[Int, Int], Map.empty[Sequent, Int])) { case ((proof, stepsMapping, importsMapping), (step, i)) =>
      step match {
        case SCImplicitProofStep(conclusion, premises, imports) =>
          val newImports = imports.foldLeft(importsMapping)((currentImports: Map[Sequent, Int], toImport: Sequent) => if(currentImports.contains(toImport)) currentImports else currentImports + (toImport -> currentImports.size))
          val usedImports = imports.map(imp => -(newImports(imp) + 1))
          val newProof = SCProofStepFinder.proofStepFinder(proof.copy(imports = newImports.toIndexedSeq.sortBy(_._2).map(_._1)), conclusion, premises.map(stepsMapping) ++ usedImports)
          val newMapping = stepsMapping + (i -> (newProof.steps.size - 1))
          (newProof, newMapping, newImports)
        case SCExplicitProofStep(scStep) =>
          val newScStep = SCUtils.mapPremises(scStep, stepsMapping)
          // TODO if subproof is matched
          val newProof = proof.withNewSteps(IndexedSeq(newScStep))
          val newMapping = stepsMapping + (i -> (newProof.steps.size - 1))
          (newProof, newMapping, importsMapping)
      }
    }
    proof
  }

  def withNewSteps(newSteps: SCHighLevelProofStep*): SCProofBuilder = SCProofBuilder(steps ++ newSteps)
}
