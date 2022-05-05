package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.proof.SCProof
import me.cassayre.florian.masterproject.front.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.{Rewrite, SCProofStep}
import me.cassayre.florian.masterproject.util.SCUtils
import me.cassayre.florian.masterproject.front.proof.sequent.{SequentDefinitions, SequentOps}

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


  sealed abstract class ProofModeStateMutator
  case object CancelPreviousTactic extends ProofModeStateMutator
  case object ResetProofMode extends ProofModeStateMutator
  sealed abstract class Tactic extends ProofModeStateMutator
  case class TacticFocusGoal(goal: Int) extends Tactic
  case class TacticRepeat(tactic: Tactic) extends Tactic
  case class TacticFallback(tactics: Seq[Tactic]) extends Tactic
  sealed abstract class TacticGoal extends Tactic
  case object TacticApplyJustification extends TacticGoal

  type ReconstructSteps = () => IndexedSeq[SCProofStep]

  abstract class TacticGoalFunctional extends TacticGoal {
    // The premises indexing is implicit:
    // * 0, 1, 2 will reference respectively the first, second and third steps in that array
    // * -1, -2, -3 will reference respectively the first second and third premises, as returned by `hypotheses`
    def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)]
  }


  trait ReadableProofEnvironment {
    def contains(sequent: Sequent): Boolean
    def belongsToTheory(sequent: SequentBase): Boolean
  }

  type ProofEnvironment <: ReadableProofEnvironment

  private case class ProofStateSnapshot(
    proofState: ProofState,
    shadowProofState: IndexedSeq[Int],
    nextId: Int,
  )

  private case class AppliedTactic(id: Int, tactic: Tactic, reconstruct: ReconstructSteps, isTheorem: Boolean)

  case class ProofModeState private[ProofStateDefinitions](
    private[ProofStateDefinitions] val initialSnapshot: ProofStateSnapshot,
    private[ProofStateDefinitions] val steps: Seq[(AppliedTactic, ProofStateSnapshot)], // Steps are in reverse direction (the first element is the latest)
    environment: ProofEnvironment,
  ) {
    private[ProofStateDefinitions] def lastSnapshot: ProofStateSnapshot =
      steps.headOption.map { case (_, snapshot) => snapshot }.getOrElse(initialSnapshot)
    private[ProofStateDefinitions] def zippedSteps: Seq[(ProofStateSnapshot, AppliedTactic, ProofStateSnapshot)] = {
      val snapshots = steps.map { case (_, snapshot) => snapshot } :+ initialSnapshot
      snapshots.zip(snapshots.tail).zip(steps.map { case (applied, _) => applied }).map {
        case ((snapshotAfter, snapshotBefore), applied) =>
          (snapshotBefore, applied, snapshotAfter)
      }
    }
    private[ProofStateDefinitions] def withNewStep(applied: AppliedTactic, nextSnapshot: ProofStateSnapshot): ProofModeState =
      copy(steps = (applied, nextSnapshot) +: steps)

    def state: ProofState = lastSnapshot.proofState
    def proving: ProofState = initialSnapshot.proofState
    def tactics: Seq[Tactic] = steps.map { case (AppliedTactic(_, tactic, _, _), _) => tactic }.reverse
  }

  def applyMutator(proofModeState: ProofModeState, mutator: ProofModeStateMutator): Option[ProofModeState] = {
    val lastSnapshot = proofModeState.lastSnapshot
    val proofState = lastSnapshot.proofState
    val shadowProofState = lastSnapshot.shadowProofState
    val nextId = lastSnapshot.nextId

    mutator match {
      case tactic: Tactic => tactic match {
        case tacticCurrentGoal: TacticGoal =>
          (proofState.goals, shadowProofState) match {
            case (proofGoal +: tailGoals, id +: tailShadowProofState) =>
              tacticCurrentGoal match {
                case TacticApplyJustification =>
                  if(proofModeState.environment.contains(proofGoal)) {
                    Some(proofModeState.withNewStep(
                      AppliedTactic(id, tactic, () => IndexedSeq.empty, true), ProofStateSnapshot(ProofState(tailGoals), tailShadowProofState, nextId)
                    ))
                  } else {
                    None
                  }
                case general: TacticGoalFunctional =>
                  general(proofGoal).map { case (steps, f) => (steps, f) }.map { case (newGoals, reconstruct) =>
                    // We prepend the newly created goals
                    val newProofState = ProofState(newGoals ++ tailGoals)
                    // Number of goals that have been created (or updated), possibly zero
                    // This corresponds to the number of premises in that rule
                    val nReplacedGoals = newProofState.goals.size - proofState.goals.size + 1
                    val newShadowGoals = nextId until (nextId + nReplacedGoals)
                    // Updated shadow proof state (= ids for the new proof state)
                    val newShadowProofState = newShadowGoals ++ tailShadowProofState
                    // Since we created n new goals, we must increment the counter by n
                    val newNextId = nextId + nReplacedGoals

                    proofModeState.withNewStep(AppliedTactic(id, tactic, reconstruct, false), ProofStateSnapshot(newProofState, newShadowProofState, newNextId))
                  }
              }
            case _ => None
          }
        case TacticRepeat(tactic) =>
          def repeat(currentState: ProofModeState, executed: Boolean): Option[ProofModeState] = {
            applyMutator(currentState, tactic) match {
              case Some(newProofModeState) => repeat(newProofModeState, true)
              case None => if(executed) Some(currentState) else None
            }
          }
          repeat(proofModeState, false)
        case TacticFallback(tactics) =>
          def iteratedTry(remaining: Seq[Tactic]): Option[ProofModeState] = remaining match {
            case tactic +: tail =>
              applyMutator(proofModeState, tactic) match {
                case Some(newProofModeState) => Some(newProofModeState)
                case None => iteratedTry(tail)
              }
            case _ => None
          }
          iteratedTry(tactics)
        case TacticFocusGoal(goal) =>
          if(proofState.goals.indices.contains(goal)) {
            // This function moves the element of index `goal` to the front
            def bringToFront[T](goals: IndexedSeq[T]): IndexedSeq[T] =
              goals(goal) +: (goals.take(goal) ++ goals.drop(goal + 1))
            val newProofState = ProofState(bringToFront(proofState.goals))
            val newShadowProofState = bringToFront(shadowProofState)
            Some(proofModeState.withNewStep(
              AppliedTactic(-1, tactic, () => IndexedSeq.empty, false), ProofStateSnapshot(newProofState, newShadowProofState, nextId)
            ))
          } else {
            None
          }
      }
      case CancelPreviousTactic =>
        proofModeState.steps match {
          case _ +: previousSteps =>
            Some(proofModeState.copy(steps = previousSteps))
          case _ => None
        }
      case ResetProofMode => Some(proofModeState.copy(steps = Seq.empty))
    }
  }

  def evaluateProof(proof: Proof)(environment: ProofEnvironment): Option[ProofModeState] = {
    def applyTactics(tactics: Seq[Tactic], proofModeState: ProofModeState): Option[ProofModeState] = tactics match {
      case tactic +: rest =>
        applyMutator(proofModeState, tactic) match {
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
      case ((proof, translation, theorems), (snapshotBefore, applied, snapshotAfter)) =>
        val reconstructedSteps = applied.reconstruct()
        val isTheorem = applied.isTheorem
        val nReplacedGoals = snapshotAfter.nextId - snapshotBefore.nextId // TODO do not rely on the ids for that
        val id = applied.id // TODO
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
  def initialProofModeState(goals: Sequent*)(environment: ProofEnvironment): ProofModeState = {
    require(goals.forall(isAcceptedSequent(_)(environment)))
    ProofModeState(ProofStateSnapshot(ProofState(goals: _*), 0 until goals.size, goals.size), Seq.empty, environment)
  }

  def isAcceptedSequent(sequent: Sequent)(environment: ProofEnvironment): Boolean = {
    isSequentWellFormed(sequent) && schematicConnectorsOfSequent(sequent).isEmpty && environment.belongsToTheory(sequent) // TODO is printable
  }

  object Notations {
    val (a, b, c, d, e) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"), SchematicPredicateLabel[0]("d"), SchematicPredicateLabel[0]("e"))
    val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
    val p: SchematicPredicateLabel[1] = SchematicPredicateLabel[1]("p")
    val (x, y) = (VariableLabel("x"), VariableLabel("y"))
  }

}
