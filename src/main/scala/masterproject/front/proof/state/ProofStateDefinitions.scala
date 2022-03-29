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
        goals.map(_.toString).map(s => s"- $s")
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

  type ProofEnvironment <: ReadableProofEnvironment

  def mutateProofGoal(proofGoal: Sequent, tactic: Tactic, proofContext: ProofEnvironment): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
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

  def mutateProofStateFirstGoal(proofState: ProofState, tactic: Tactic, proofContext: ProofEnvironment): Option[(ProofState, ReconstructGeneral)] = {
    proofState.goals match {
      case h +: t =>
        mutateProofGoal(h, tactic, proofContext).map { (newGoals, ctx) => (ProofState(newGoals ++ t), ctx) }
      case _ => None
    }
  }

  private case class ProofStateSnapshot(
    proofState: ProofState,
    shadowProofState: IndexedSeq[Int],
    nextId: Int,
  )
  case class ProofModeState private[ProofStateDefinitions](
    private[ProofStateDefinitions] val initialSnapshot: ProofStateSnapshot,
    private[ProofStateDefinitions] val steps: Seq[((Tactic, ReconstructGeneral), ProofStateSnapshot)], // Steps are in reverse direction (the first element is the latest)
    environment: ProofEnvironment,
  ) {
    private[ProofStateDefinitions] def lastSnapshot: ProofStateSnapshot =
      steps.headOption.map { case (_, snapshot) => snapshot }.getOrElse(initialSnapshot)
    private[ProofStateDefinitions] def zippedSteps: Seq[(ProofStateSnapshot, (Tactic, ReconstructGeneral), ProofStateSnapshot)] = {
      val snapshots = steps.map { case (_, snapshot) => snapshot } :+ initialSnapshot
      snapshots.zip(snapshots.tail).zip(steps.map { case (pair, _) => pair }).map {
        case ((snapshotAfter, snapshotBefore), pair) =>
          (snapshotBefore, pair, snapshotAfter)
      }
    }
    private[ProofStateDefinitions] def withNewStep(tactic: Tactic, reconstruct: ReconstructGeneral, nextSnapshot: ProofStateSnapshot): ProofModeState =
      copy(steps = ((tactic, reconstruct), nextSnapshot) +: steps)

    def state: ProofState = lastSnapshot.proofState
    def proving: ProofState = initialSnapshot.proofState
    def tactics: Seq[Tactic] = steps.map { case ((tactic, _), _) => tactic }.reverse
  }

  def applyTactic(proofModeState: ProofModeState, tactic: Tactic): Option[ProofModeState] = {
    val lastSnapshot = proofModeState.lastSnapshot
    val proofState = lastSnapshot.proofState
    val shadowProofState = lastSnapshot.shadowProofState
    val nextId = lastSnapshot.nextId
    mutateProofStateFirstGoal(proofModeState.lastSnapshot.proofState, tactic, proofModeState.environment).map {
      case (newState, reconstructFunction) =>
        // The id of the goal that was transformed (here, it's always the first one)
        val id = shadowProofState.head
        val updatedGoal = proofState.goals.head
        // Number of goals that have been created (or updated), possibly zero
        // This corresponds to the number of premises in that rule
        val nReplacedGoals = newState.goals.size - proofState.goals.size + 1
        val newShadowGoals = nextId until (nextId + nReplacedGoals)
        // Updated shadow proof state (= ids for the new proof state)
        val newShadowProofState = newShadowGoals ++ shadowProofState.tail
        // Since we created n new goals, we must increment the counter by n
        val newNextId = nextId + nReplacedGoals

        proofModeState.withNewStep(tactic, reconstructFunction, ProofStateSnapshot(newState, newShadowProofState, newNextId))
    }
  }

  def evaluateProof(proof: Proof)(environment: ProofEnvironment): Option[ProofModeState] = {
    def applyTactics(tactics: Seq[Tactic], proofModeState: ProofModeState): Option[ProofModeState] = tactics match {
      case tactic +: rest =>
        applyTactic(proofModeState, tactic) match {
          case Some(newProofModeState) => applyTactics(rest, newProofModeState)
          case None => None
        }
      case _ => Some(proofModeState)
    }
    applyTactics(proof.steps, initialProofModeState(proof.initialState.goals: _*)(environment))
  }

  def reconstructSCProof(proofModeState: ProofModeState): (SCProof, Map[Int, Sequent]) = {
    val proofEnvironment = proofModeState.environment
    // Each proof goal that is created (or updated) will be given a unique id
    // Then we use these ids to refer to them as a proof step in the SC proof

    // For a complete proof the proof state should be empty
    // However for testing purposes we may still allow incomplete proofs to exist,
    // and for that we should convert unclosed branches into imports
    val imports = proofModeState.lastSnapshot.proofState.goals.map(sequentToKernel)
    val initialTranslation = proofModeState.lastSnapshot.shadowProofState.zipWithIndex.map { case (v, i) => v -> -(i + 1) }.toMap

    val (finalProof, _, finalTheorems) = proofModeState.zippedSteps.foldLeft((SCProof(IndexedSeq.empty, imports), initialTranslation, Map.empty[Int, Sequent])) {
      case ((proof, translation, theorems), (snapshotBefore, (tactic, reconstruct), snapshotAfter)) =>
        val (reconstructedSteps, isTheorem) = tactic match { // TODO we have a repetition here
          case TacticApplyTheorem =>
            (IndexedSeq.empty, true)
          case general: GeneralTactic =>
            (reconstruct(), false)
        }
        val nReplacedGoals = snapshotAfter.nextId - snapshotBefore.nextId // TODO do not rely on the ids for that
        val id = snapshotBefore.shadowProofState.head // TODO
        val updatedGoal = snapshotBefore.proofState.goals.head
        // We need to "fix" the indexing of these proof steps
        def premiseMapping(p: Int): Int = {
          if(p < 0) {
            val i = Math.abs(p) - 1
            assert(i < nReplacedGoals)
            val selectedGoalId = snapshotAfter.shadowProofState(i)
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
          (
            newProof.copy(imports = newProof.imports :+ sequentToKernel(updatedGoal)),
            translation + (id -> translatedId),
            theorems + (importId -> updatedGoal),
          )
        } else {
          val translatedId = newProof.steps.size - 1
          (
            newProof,
            translation + (id -> translatedId),
            theorems,
          )
        }
    }

    (finalProof, finalTheorems)
  }

  // The final conclusion is given the id 0, although it will never be referenced as a premise
  def initialProofModeState(goals: Sequent*)(environment: ProofEnvironment): ProofModeState =
    ProofModeState(ProofStateSnapshot(ProofState(goals: _*), 0 until goals.size, goals.size), Seq.empty, environment)

  object Notations {
    val (a, b, c, d, e) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"), SchematicPredicateLabel[0]("d"), SchematicPredicateLabel[0]("e"))
    val (s, t) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"))
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
    val p: SchematicPredicateLabel[1] = SchematicPredicateLabel[1]("p")
    val (x, y) = (VariableLabel("x"), VariableLabel("y"))
  }

}
