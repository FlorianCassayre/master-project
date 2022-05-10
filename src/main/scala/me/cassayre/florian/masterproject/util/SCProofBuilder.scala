package me.cassayre.florian.masterproject.util

import lisa.kernel.proof.{SCProof, SequentCalculus}
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.Axiom

/**
 * The proof builder API, a helper to build kernel proofs.
 */
object SCProofBuilder {
  /**
   * A higher-level proof step, can represent several kernel proof steps at once.
   */
  sealed abstract class SCHighLevelProofStep

  /**
   * An implicit proof step, namely a step for which only the conclusion an premises have to be specified.
   * This step will try to be reconstructed into a single kernel proof step.
   * @param conclusion the conclusion the kernel step should have
   * @param premises a superset of premises that should appear in the kernel step
   * @param imports optional imports to be used (or added to the proof)
   */
  case class SCImplicitProofStep(conclusion: Sequent, premises: Seq[Int] = Seq.empty, imports: Seq[Sequent] = Seq.empty) extends SCHighLevelProofStep
  /**
   * An explicit proof step, namely a wrapper for a kernel proof step.
   * @param step the kernel proof step
   */
  case class SCExplicitProofStep(step: SCProofStep) extends SCHighLevelProofStep

  /**
   * Creates a new proof builder with the provided steps.
   * @param steps the steps to be used by this builder
   * @return a new new proof builder
   */
  def apply(steps: SCHighLevelProofStep*): SCProofBuilder = new SCProofBuilder(steps.toIndexedSeq)

  implicit class SequentBy(s: Sequent) {
    infix def by(premises: Int*): SCImplicitProofStep = SCImplicitProofStep(s, premises, Seq.empty)
    infix def by(step: SCProofStep): SCExplicitProofStep = SCExplicitProofStep(step)
    infix def justifiedBy(sequents: Sequent*): SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, sequents)
    infix def justifiedBy(axiom: Axiom): SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, Seq(Sequent(Set.empty, Set(axiom))))
    def justified: SCImplicitProofStep = SCImplicitProofStep(s, Seq.empty, Seq(s))
  }

  given Conversion[Sequent, SCImplicitProofStep] = SCImplicitProofStep(_, Seq.empty, Seq.empty)
}

import me.cassayre.florian.masterproject.util.SCProofBuilder.*

/**
 * The proof builder.
 * @param steps the steps currently in this builder
 */
case class SCProofBuilder(steps: IndexedSeq[SCHighLevelProofStep]) {

  /**
   * Builds the proof in this builder.
   * @return the built proof
   */
  def build: SCProof = {
    // (proof, indices mapping, imports mapping)
    val (proof, _, _) = steps.zipWithIndex.foldLeft((SCProof.apply(), Map.empty[Int, Int], Map.empty[Sequent, Int])) { case ((proof, stepsMapping, importsMapping), (step, i)) =>
      step match {
        case SCImplicitProofStep(conclusion, premises, imports) =>
          val newImports = imports.foldLeft(importsMapping)((currentImports: Map[Sequent, Int], toImport: Sequent) => if(currentImports.contains(toImport)) currentImports else currentImports + (toImport -> currentImports.size))
          val usedImports = imports.map(imp => -(newImports(imp) + 1))
          SCProofStepFinder.proofStepFinder(proof.copy(imports = newImports.toIndexedSeq.sortBy(_._2).map(_._1)), conclusion, premises.map(stepsMapping) ++ usedImports) match {
            case Some(newProof) =>
              val newMapping = stepsMapping + (i -> (newProof.steps.size - 1))
              (newProof, newMapping, newImports)
            case None =>
              throw new Exception("Implicit proof step could not be reconstructed")
          }
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

  /**
   * Add several new steps to that builder.
   * @param newSteps the steps to be added
   * @return the new builder with these steps
   */
  def withNewSteps(newSteps: SCHighLevelProofStep*): SCProofBuilder = SCProofBuilder(steps ++ newSteps)
}
