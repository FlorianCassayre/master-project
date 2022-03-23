package masterproject.front.proof.state

import lisa.kernel.proof.SCProof
import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.{Rewrite, SCProofStep}
import masterproject.SCUtils
import masterproject.front.proof.sequent.{SequentDefinitions, SequentOps}

trait ProofStateDefinitions extends SequentDefinitions with SequentOps {

  case class Proof(initialState: ProofState, steps: Seq[Tactic])
  object Proof {
    def apply(goals: Sequent*)(steps: Tactic*): Proof = Proof(ProofState(goals.toIndexedSeq), steps)
  }

  final case class ProofState(goals: IndexedSeq[Sequent]) {
    override def toString: String =
      ((if (goals.nonEmpty) s"${goals.size} goal${if (goals.sizeIs > 1) "s" else ""}" else "[zero goals]") +:
        goals.map(_.toString)
        ).mkString("\n")
  }
  object ProofState {
    def apply(goals: Sequent*): ProofState = ProofState(goals.toIndexedSeq)
  }

  sealed abstract class Tactic

  case object TacticApplyTheorem extends Tactic

  type ReconstructGeneral = () => IndexedSeq[SCProofStep]

  abstract class GeneralTactic extends Tactic {
    // The premises indexing is implicit:
    // * 0, 1, 2 will reference respectively the first, second and third steps in that array
    // * -1, -2, -3 will reference respectively the first second and third premises, as returned by `hypotheses`
    def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructGeneral)]
  }

  trait ReadableProofEnvironment {
    def contains(sequent: Sequent): Boolean
  }

  def mutateProofGoal(proofGoal: Sequent, tactic: Tactic, proofContext: ReadableProofEnvironment): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
    tactic match {
      case TacticApplyTheorem =>
        if(proofContext.contains(proofGoal)) {
          Some((
            IndexedSeq.empty,
            () => IndexedSeq.empty, // TODO exception?
          ))
        } else {
          None
        }
      case general: GeneralTactic =>
        general(proofGoal).map { case (steps, f) => (steps, f) }
    }
  }

  def mutateProofStateFirstGoal(proofState: ProofState, tactic: Tactic, proofContext: ReadableProofEnvironment): Option[(ProofState, ReconstructGeneral)] = {
    proofState.goals match {
      case h +: t =>
        mutateProofGoal(h, tactic, proofContext).map { (newGoals, ctx) => (ProofState(newGoals ++ t), ctx) }
      case _ => None
    }
  }

  def reconstructSCProof(proof: Proof, proofEnvironment: ReadableProofEnvironment): Option[(SCProof, Map[Int, Sequent])] = {
    // Each proof goal that is created (or updated) will be given a unique id
    // Then we use these ids to refer to them as a proof step in the SC proof
    def recursive(nextId: Int, shadowProofState: IndexedSeq[Int], proofState: ProofState, remaining: Seq[Tactic]): Option[(SCProof, Map[Int, Int], Map[Int, Sequent])] = remaining match {
      case tactic +: rest =>
        mutateProofStateFirstGoal(proofState, tactic, proofEnvironment) match {
          case Some((newState, reconstructFunction)) =>
            // The id of the goal that was transformed (here, it's always the first one)
            val id = shadowProofState.head
            val updatedGoal = proofState.goals.head
            // Number of goals that have been created (or updated), possibly zero
            // This corresponds to the number of premises in that rule
            val nReplacedGoals = newState.goals.size - proofState.goals.size + 1
            val newShadowGoals = nextId until (nextId + nReplacedGoals)
            // Updated shadow proof state (= ids for the new proof state)
            val newShadowProofState = newShadowGoals ++ shadowProofState.tail
            // We continue exploring the tree. The reconstruction happens when this function returns
            recursive(nextId + nReplacedGoals, newShadowProofState, newState, rest) match {
              case Some((proof, translation, theorems)) =>
                // Now we can reconstruct the SC proof steps
                val (reconstructedSteps, isTheorem) = tactic match { // TODO fix this ugly wart
                  case TacticApplyTheorem =>
                    (IndexedSeq.empty, true)
                  case general: GeneralTactic =>
                    (reconstructFunction(), false)
                  case e => throw new MatchError(e)
                }
                // We need to "fix" the indexing of these proof steps
                def premiseMapping(p: Int): Int = {
                  if(p < 0) {
                    val i = Math.abs(p) - 1
                    assert(i < nReplacedGoals)
                    val selectedGoalId = newShadowGoals(i)
                    translation(selectedGoalId)
                  } else {
                    assert(p < reconstructedSteps.size - 1)
                    proof.steps.size + p
                  }
                }
                val reconstructedAndRemappedSteps = reconstructedSteps.map(SCUtils.mapPremises(_, premiseMapping))
                val newProof = proof.withNewSteps(reconstructedAndRemappedSteps)
                // We return the expanded proof, along with the information to recover the last (= current) step as a premise
                if(isTheorem) {
                  val importId = newProof.imports.size
                  val translatedId = -(importId + 1)
                  Some((
                    newProof.copy(imports = newProof.imports :+ sequentToKernel(updatedGoal)),
                    translation + (id -> translatedId),
                    theorems + (importId -> updatedGoal),
                  ))
                } else {
                  val translatedId = newProof.steps.size - 1
                  Some((
                    newProof,
                    translation + (id -> translatedId),
                    theorems,
                  ))
                }

              case None => None
            }
          case None =>
            None
        }
      case _ => // Bottom of the front proof, now we go the other way
        // For a complete proof the proof state should be empty
        // However for testing purposes we may still allow incomplete proofs to exist,
        // and for that we should convert unclosed branches into imports
        val imports = proofState.goals.map(sequentToKernel)
        val initialTranslation = shadowProofState.zipWithIndex.map { case (v, i) => v -> -(i + 1) }.toMap
        Some((SCProof(IndexedSeq.empty, imports), initialTranslation, Map.empty))
    }
    // The final conclusion is given the id 0, although it will never be referenced as a premise
    recursive(proof.initialState.goals.size, proof.initialState.goals.indices, proof.initialState, proof.steps).map { case (proof, _, theorems) => (proof, theorems) }
  }

  object Notations {
    val (a, b, c, d, e) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"), SchematicPredicateLabel[0]("d"), SchematicPredicateLabel[0]("e"))
    val (s, t) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"))
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
    val p: SchematicPredicateLabel[1] = SchematicPredicateLabel[1]("p")
    val x: VariableLabel = VariableLabel("x")
  }

}
