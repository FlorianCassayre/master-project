package me.cassayre.florian.masterproject.util

import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.SCProof

/**
 * Utilities to work with sequent-calculus proofs.
 */
object SCUtils {

  /**
   * Computes the size of a proof. Size corresponds to the number of proof steps.
   * Subproofs are count as one plus the size of their body.
   * @param proof the proof to analyze
   * @return the size of that proof
   */
  def proofSize(proof: SCProof): Int =
    proof.steps.map {
      case SCSubproof(sp, _, _) => 1 + proofSize(sp)
      case _ => 1
    }.sum

  /**
   * Computes the depth of a proof. Depth corresponds to the maximum number of nested subproofs plus one.
   * @param proof the proof to analyze
   * @return the depth of that proof
   */
  def proofDepth(proof: SCProof): Int =
    proof.steps.map {
      case SCSubproof(sp, _, _) => 1 + proofDepth(sp)
      case _ => 1
    }.max

  /**
   * Updates the indices of the premises in a proof step according to some provided mapping. For example:
   * <pre>
   * mapPremises(Rewrite(sequent, 1), i => i + 1) == Rewrite(sequent, 2)
   * </pre>
   * @param step the proof step to update
   * @param mapping the provided mapping
   * @return a new step with the updated indices
   */
  def mapPremises(step: SCProofStep, mapping: Int => Int): SCProofStep = step match {
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
    case s: InstFunSchema => s.copy(t1 = mapping(s.t1))
    case s: InstPredSchema => s.copy(t1 = mapping(s.t1))
  }

  /**
   * Flattens a proof recursively; in other words it removes all occurrences of [[SCSubproof]].
   * The order of proof steps is preserved, indices of premises are adapted to reflect the new ordering.
   * Assumes that the provided proof is well-formed (but not necessarily valid).
   * If the provided proof is valid, then the resulting proof will also be valid.
   * @param proof the proof to be flattened
   * @return the flattened proof
   */
  def flattenProof(proof: SCProof): SCProof = {
    def flattenProofRecursive(steps: IndexedSeq[SCProofStep], topPremises: IndexedSeq[Int], offset: Int): IndexedSeq[SCProofStep] = {
      val (finalAcc, _) = steps.foldLeft((IndexedSeq.empty[SCProofStep], IndexedSeq.empty[Int])) { case ((acc, localToGlobal), step) =>
        def resolve(i: Int): Int = if(i >= 0) localToGlobal(i) else topPremises(-i - 1)
        val newAcc = step match {
          case SCSubproof(subProof, subPremises, _) =>
            acc ++ flattenProofRecursive(subProof.steps, subPremises.map(resolve).toIndexedSeq, acc.size)
          case _ =>
            acc :+ mapPremises(step, resolve)
        }
        (newAcc, localToGlobal :+ (offset + newAcc.size - 1))
      }
      finalAcc
    }
    SCProof(flattenProofRecursive(proof.steps, proof.imports.indices.map(-_ - 1), 0), proof.imports)
  }

  /**
   * Eliminates all steps that are not indirectly referenced by the conclusion (last step) of the proof.
   * This procedure is applied recursively on all subproofs. The elimination of unused top-level imports can be configured.
   * The order of proof steps is preserved, indices of premises are adapted to reflect the new ordering.
   * Assumes that the provided proof is well-formed (but not necessarily valid).
   * If the provided proof is valid, then the resulting proof will also be valid.
   * @param proof the proof to be simplified
   * @param eliminateTopLevelDeadImports whether the unused top-level imports should be eliminated as well
   * @return the proof with dead steps eliminated
   */
  def deadStepsElimination(proof: SCProof, eliminateTopLevelDeadImports: Boolean = true): SCProof = {
    def deadStepsEliminationInternal(proof: SCProof, eliminateDeadImports: Boolean): (SCProof, IndexedSeq[Int]) = {
      // We process the leaves first, otherwise we could miss dead branches (subproofs that more imports than necessary)
      val processedSteps = proof.steps.map {
        case SCSubproof(sp, premises, display) =>
          val (newSubProof, newImportsIndices) = deadStepsEliminationInternal(sp, true)
          SCSubproof(newSubProof, newImportsIndices.map(premises), display)
        case other => other
      }
      val graph = processedSteps.map(_.premises)
      val nodes = graph.indices
      def bfs(visited: Set[Int], toVisit: Set[Int]): Set[Int] = {
        if(toVisit.nonEmpty) {
          val next = toVisit.flatMap(graph).diff(visited)
          bfs(visited ++ next, next.filter(_ >= 0))
        } else {
          visited
        }
      }
      val conclusionNode = nodes.last // Must exist by assumption
      val visited = bfs(Set(conclusionNode), Set(conclusionNode))
      val newNodes = nodes.filter(visited.contains)
      val newImports = proof.imports.indices.map(i => -(i + 1)).filter(i => !eliminateDeadImports || visited.contains(i))
      val newImportsIndices = newImports.map(i => -(i + 1))
      val oldToNewStep = newNodes.zipWithIndex.toMap
      val oldToNewImport = newImports.zipWithIndex.map { case (i, j) => (i, -(j + 1)) }.toMap
      val map = oldToNewStep ++ oldToNewImport
      val newSteps = newNodes.map(processedSteps).map(step => mapPremises(step, map))
      val newProof = SCProof(newSteps, newImportsIndices.map(proof.imports))
      (newProof, newImportsIndices)
    }
    val (newProof, _) = deadStepsEliminationInternal(proof, eliminateTopLevelDeadImports)
    newProof
  }

}
