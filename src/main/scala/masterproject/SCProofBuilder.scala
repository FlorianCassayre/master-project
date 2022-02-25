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
  private def mapPremises(step: SCProofStep, mapping: Int => Int): SCProofStep = step match {
    case s: Rewrite => s.copy(t1 = mapping(s.t1))
    case s: Hypothesis => s
    case s: Cut => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftAnd => s.copy(t1 = mapping(s.t1))
    case s: LeftOr => s.copy(t = s.t.map(mapping))
    case s: LeftImplies => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftIff => s.copy(t1 = mapping(s.t1))
    case s: LeftNot => s.copy(t1 = mapping(s.t1))
    case s: LeftForall => s.copy(t1 = mapping(s.t1))
    case s: LeftExists => s.copy(t1 = mapping(s.t1))
    case s: LeftExistsOne => s.copy(t1 = mapping(s.t1))
    case s: RightAnd => s.copy(t = s.t.map(mapping))
    case s: RightOr => s.copy(t1 = mapping(s.t1))
    case s: RightImplies => s.copy(t1 = mapping(s.t1))
    case s: RightIff => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: RightNot => s.copy(t1 = mapping(s.t1))
    case s: RightForall => s.copy(t1 = mapping(s.t1))
    case s: RightExists => s.copy(t1 = mapping(s.t1))
    case s: RightExistsOne => s.copy(t1 = mapping(s.t1))
    case s: Weakening => s.copy(t1 = mapping(s.t1))
    case s: LeftRefl => s.copy(t1 = mapping(s.t1))
    case s: RightRefl => s
    case s: LeftSubstEq => s.copy(t1 = mapping(s.t1))
    case s: RightSubstEq => s.copy(t1 = mapping(s.t1))
    case s: LeftSubstIff => s.copy(t1 = mapping(s.t1))
    case s: RightSubstIff => s.copy(t1 = mapping(s.t1))
    case s: SCSubproof => s.copy(premises = s.premises.map(mapping))
  }

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
          val newScStep = mapPremises(scStep, stepsMapping)
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
