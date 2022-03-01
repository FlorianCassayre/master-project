package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.Printer.*
import lisa.kernel.proof.SequentCalculus.{Sequent, sequentToFormula, Hypothesis, Weakening}
import lisa.kernel.proof.{SCProof, SCProofChecker}
import masterproject.SCProofBuilder
import masterproject.SCProofBuilder.{SCExplicitProofStep, SCHighLevelProofStep, SCImplicitProofStep}
import proven.tactics.SimplePropositionalSolver

object GoalBasedProofSystem {

  case class ProofGoal(hypotheses: IndexedSeq[Formula], goal: Formula)
  case class ProofState(goals: IndexedSeq[ProofGoal])

  sealed abstract class ProofGoalUpdate
  case class UpdateGoal(newGoal: Formula, newHypotheses: IndexedSeq[Formula]) extends ProofGoalUpdate
  case class UpdateHypothesis(hypothesisIndex: Int, newHypotheses: IndexedSeq[Formula]) extends ProofGoalUpdate

  case class ProofStateDiff(goalIndex: Int = 0, replacement: IndexedSeq[ProofGoalUpdate])

  /*
  Each tactic can update one `ProofGoal` at a time.
  An update of a `ProofGoal` replaces that object by any number of new instances of `ProofGoal`.
  A `ProofGoal` can only be updated through `ProofGoalDiff`.
  A `ProofGoalDiff` can do one of the following:
  - Set the goal formula to a new formula
  - Replace an hypothesis formula by a sequence of formulas
  */

  type ReconstructionCallback = PartialFunction[(Sequent, Seq[Int]), IndexedSeq[SCHighLevelProofStep]]

  case class TacticResult(diff: ProofStateDiff, reconstruct: ReconstructionCallback = (sequent, premises) => IndexedSeq(SCImplicitProofStep(sequent, premises)))

  abstract class Tactic {
    def apply(state: ProofState): Option[TacticResult]
  }

  abstract class TacticDefaultGoal extends Tactic {
    override final def apply(state: ProofState): Option[TacticResult] =
      apply(state.goals(0))
    def apply(state: ProofGoal): Option[TacticResult]
  }

  case object TacticAssume extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      state.goal match {
        case ConnectorFormula(`Implies`, Seq(a, b)) =>
          Some(TacticResult(
            ProofStateDiff(replacement = IndexedSeq(UpdateGoal(b, IndexedSeq(a)))),
            // Example:
            //{ case (sequent, Seq(t1)) => IndexedSeq(SCImplicitProofStep(sequent, Seq(t1))) }
            // Since we're using an implicit step we can optionally omit it
          ))
        case _ => None
      }
  }

  case class TacticWeakenHypothesis(hypothesisIndex: Int) extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(UpdateHypothesis(hypothesisIndex, IndexedSeq())))))
  }

  case object TacticEliminate extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      if(state.hypotheses.exists(isSame(_, state.goal))) {
        Some(
          TacticResult(ProofStateDiff(replacement = IndexedSeq.empty), {
            case (sequent, Seq()) =>
              val hypothesis = SCExplicitProofStep(Hypothesis(Sequent(sequent.right, sequent.right), sequent.right.head))
              if(sequent.left.sizeIs > 1) {
                IndexedSeq(
                  hypothesis,
                  SCExplicitProofStep(Weakening(sequent, 0))
                )
              } else {
                IndexedSeq(hypothesis)
              }
          })
        )
      } else {
        None
      }
  }

  case class TacticDestructHypothesis(hypothesisIndex: Int) extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      state.hypotheses(hypothesisIndex) match {
        case ConnectorFormula(`And`, seq) if seq.sizeIs >= 2 =>
          Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
            UpdateHypothesis(hypothesisIndex, IndexedSeq(seq.head, if(seq.sizeIs == 2) seq.tail.head else ConnectorFormula(`And`, seq.tail))),
          ))))
        case ConnectorFormula(`Iff`, Seq(a, b)) =>
          Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
            UpdateHypothesis(hypothesisIndex, IndexedSeq(ConnectorFormula(Implies, Seq(a, b)), ConnectorFormula(Implies, Seq(b, a))))
          ))))
        case _ => None
      }
  }

  case object TacticDestructGoal extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      state.goal match {
        case ConnectorFormula(`And`, seq) if seq.sizeIs >= 2 =>
          Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
            UpdateGoal(seq.head, IndexedSeq.empty),
            UpdateGoal(if(seq.sizeIs == 2) seq.tail.head else ConnectorFormula(And, seq.tail), IndexedSeq.empty)
          ))))
        case ConnectorFormula(`Iff`, Seq(a, b)) =>
          Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
            UpdateGoal(ConnectorFormula(Implies, Seq(a, b)), IndexedSeq.empty),
            UpdateGoal(ConnectorFormula(Implies, Seq(b, a)), IndexedSeq.empty)
          ))))
        case _ => None
      }
  }

  case class TacticOrHypothesis(hypothesisIndex: Int) extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      state.hypotheses(hypothesisIndex) match {
        case ConnectorFormula(`Or`, Seq(a, b)) => Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
          UpdateHypothesis(hypothesisIndex, IndexedSeq(a)),
          UpdateHypothesis(hypothesisIndex, IndexedSeq(b)),
        ))))
        case _ => None
      }
  }

  case class TacticOrNGoal(n: Int) extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] =
      state.goal match {
        case ConnectorFormula(`Or`, seq) if seq.sizeIs >= 2 && seq.indices.contains(n) => Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
          UpdateGoal(seq(n), IndexedSeq.empty),
        ))))
        case _ => None
      }
  }

  case object TacticPropositionalSolver extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] = {
      val sequent = proofGoalToSequent(state)
      val proof = SimplePropositionalSolver.solveSequent(sequent)
      Some(
        TacticResult(
          ProofStateDiff(replacement = IndexedSeq.empty),
          { case (sequent, Seq()) => proof.steps.map(SCExplicitProofStep.apply) }
        )
      )
    }
  }

  case object TacticInstantiateForall extends TacticDefaultGoal {
    override def apply(state: ProofGoal): Option[TacticResult] = {
      state.goal match {
        case BinderFormula(`Forall`, _, inner) =>
          Some(TacticResult(ProofStateDiff(replacement = IndexedSeq(
            UpdateGoal(inner, IndexedSeq.empty),
          ))))
        case _ => None
      }
    }
  }

  def prettyProofGoal(proofGoal: ProofGoal): String = {
    val hypothesesStr = proofGoal.hypotheses.map(Printer.prettyFormula(_))
    val goalStr = Printer.prettyFormula(proofGoal.goal)
    val maxLength = (hypothesesStr :+ goalStr).map(_.length).max
    (hypothesesStr :+ ("=" * maxLength).mkString :+ goalStr).mkString("\n")
  }

  def prettyProofState(proofState: ProofState): String = {
    if(proofState.goals.isEmpty) {
      "[no goals left]"
    } else {
      proofState.goals.zipWithIndex.map { case (goal, i) =>
        Seq(s"goal #$i:", prettyProofGoal(goal)).mkString("\n")
      }.mkString("\n\n")
    }
  }

  def prettyFrame(string: String, verticalPadding: Int = 0, horizontalPadding: Int = 2): String = {
    val (space, vertical, horizontal, corner) = (' ', '|', '-', '+')
    val lines = string.split("\n")
    val maxLength = lines.map(_.length).max
    val bottomAndTop = (corner +: Seq.fill(maxLength + 2 * horizontalPadding)(horizontal) :+ corner).mkString
    val bottomAndTopMargin = (vertical +: Seq.fill(maxLength + 2 * horizontalPadding)(space) :+ vertical).mkString
    val linesMargin = lines.map(line => Seq(vertical) ++ Seq.fill(horizontalPadding)(space) ++ line.toCharArray ++ Seq.fill(maxLength - line.length + horizontalPadding)(space) ++ Seq(vertical)).map(_.mkString)
    (Seq(bottomAndTop) ++ Seq.fill(verticalPadding)(bottomAndTopMargin) ++ linesMargin ++ Seq.fill(verticalPadding)(bottomAndTopMargin) ++ Seq(bottomAndTop)).mkString("\n")
  }

  def replaceInArray[T](array: IndexedSeq[T], i: Int, replacement: IndexedSeq[T]): IndexedSeq[T] =
    array.take(i) ++ replacement ++ array.drop(i + 1)

  def mutateState(state: ProofState, tacticResult: TacticResult): ProofState = {
    val diff = tacticResult.diff
    val goal = state.goals(diff.goalIndex)
    val added = diff.replacement.map {
      case UpdateGoal(newGoal, newHypotheses) =>
        ProofGoal(goal.hypotheses ++ newHypotheses, newGoal)
      case UpdateHypothesis(hypothesisIndex, newHypotheses) =>
        goal.copy(hypotheses = replaceInArray(goal.hypotheses, hypothesisIndex, newHypotheses))
    }
    ProofState(replaceInArray(state.goals, diff.goalIndex, added))
  }

  def proofGoalToSequent(proofGoal: ProofGoal): Sequent = Sequent(proofGoal.hypotheses.toSet, Set(proofGoal.goal))
  def formulaToSequent(formula: Formula): Sequent = Sequent(Set.empty, Set(formula))
  def formulaToProofState(formula: Formula): ProofState = ProofState(IndexedSeq(ProofGoal(IndexedSeq.empty, formula)))

  // translation: id -> proof_step
  def recursiveReconstruction(nextId: Int, state: ProofState, seq: Seq[Tactic], proof: SCProofBuilder, shadow: IndexedSeq[Int], translation: Map[Int, Int]): (SCProofBuilder, Map[Int, Int]) = {
    seq match {
      case tactic +: t =>
        val result = tactic(state).get
        val newState = mutateState(state, result)
        val updatedGoalIndex = result.diff.goalIndex
        val id = shadow(updatedGoalIndex)
        val replacementIds = result.diff.replacement.indices.map(_ + nextId)
        val newShadow = replaceInArray(shadow, updatedGoalIndex, replacementIds)
        val newNextId = nextId + result.diff.replacement.size
        val (recursiveProof, recursiveTranslation) = recursiveReconstruction(newNextId, newState, t, proof, newShadow, translation)
        val stepIndex = recursiveProof.steps.size
        val premises = replacementIds.map(recursiveTranslation)
        val sequent = proofGoalToSequent(state.goals(updatedGoalIndex))
        val indicesOffset = recursiveProof.steps.size
        val reconstructedSteps = result.reconstruct(sequent, premises.map(_ - indicesOffset))
        val reconstructedStepsWithCorrectIndices = reconstructedSteps.map {
          case SCImplicitProofStep(conclusion, premises, imports) =>
            SCImplicitProofStep(conclusion, premises.map(_ + indicesOffset), imports) // TODO
          case SCExplicitProofStep(step) => SCExplicitProofStep(SCUtils.mapPremises(step, _ + indicesOffset))
        }
        val newProofWithNewStep = recursiveProof.withNewSteps(reconstructedStepsWithCorrectIndices: _*)
        (newProofWithNewStep, recursiveTranslation + (id -> (newProofWithNewStep.steps.size - 1)))
      case _ =>
        (proof, translation)
    }
  }

  def reconstructProof(conclusion: Formula, seq: Seq[Tactic]): SCProofBuilder =
    recursiveReconstruction(1, formulaToProofState(conclusion), seq, SCProofBuilder(), IndexedSeq(0), Map.empty)._1
}
