package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.Printer.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.{SCProof, SCProofChecker}
import masterproject.SCProofBuilder
import masterproject.SCProofBuilder.SCAnyProofStep

case class ProofGoal(hypotheses: IndexedSeq[Formula], goal: Formula)
case class ProofState(goals: IndexedSeq[ProofGoal])

sealed abstract class ProofGoalDiff
case class ProofGoalUpdateGoal(newGoal: Formula, newHypotheses: IndexedSeq[Formula]) extends ProofGoalDiff
case class ProofGoalUpdateHypothesis(hypothesisIndex: Int, newHypotheses: IndexedSeq[Formula]) extends ProofGoalDiff

case class ProofStateDiff(goalIndex: Int, replacement: IndexedSeq[ProofGoalDiff])

/*
Each tactic can update one `ProofGoal` at a time.
An update of a `ProofGoal` replaces that object by any number of new instances of `ProofGoal`.
A `ProofGoal` can only be updated through `ProofGoalDiff`.
A `ProofGoalDiff` can do one of the following:
- Set the goal formula to a new formula
- Replace an hypothesis formula by a sequence of formulas
*/

case class TacticResult(diff: ProofStateDiff /*, f: ShadowProof => ShadowProof*/)

abstract class Tactic {
  def apply(state: ProofState): Option[TacticResult]
}

case class TacticAssume(goalIndex: Int) extends Tactic {
  override def apply(state: ProofState): Option[TacticResult] = {
    state.goals(goalIndex).goal match {
      case ConnectorFormula(`Implies`, Seq(a, b)) =>
        Some(TacticResult(ProofStateDiff(goalIndex, IndexedSeq(ProofGoalUpdateGoal(b, IndexedSeq(a))))))
      case _ => None
    }
  }
}

case class TacticWeakenHypothesis(goalIndex: Int, hypothesisIndex: Int) extends Tactic {
  override def apply(state: ProofState): Option[TacticResult] =
    Some(TacticResult(ProofStateDiff(goalIndex, IndexedSeq(ProofGoalUpdateHypothesis(hypothesisIndex, IndexedSeq())))))
}

case class TacticEliminate(goalIndex: Int) extends Tactic {
  override def apply(state: ProofState): Option[TacticResult] = {
    val objective = state.goals(goalIndex)
    val goal = objective.goal
    objective.hypotheses match {
      case Seq(`goal`) =>
        Some(TacticResult(ProofStateDiff(goalIndex, IndexedSeq.empty)))
      case _ => None
    }
  }
}

case class TacticDestructHypothesis(goalIndex: Int, hypothesisIndex: Int) extends Tactic {
  override def apply(state: ProofState): Option[TacticResult] = {
    val objective = state.goals(goalIndex)
    val hypothesis = objective.hypotheses(hypothesisIndex)
    hypothesis match {
      case ConnectorFormula(`And`, seq) if seq.sizeIs >= 2 =>
        Some(TacticResult(ProofStateDiff(goalIndex, IndexedSeq(
          ProofGoalUpdateHypothesis(hypothesisIndex, IndexedSeq(seq.head, if(seq.sizeIs == 2) seq.tail.head else ConnectorFormula(`And`, seq.tail))),
        ))))
      case _ => None
    }
  }
}

case class TacticOrLeftHypothesis(goalIndex: Int, hypothesisIndex: Int) extends Tactic {
  override def apply(state: ProofState): Option[TacticResult] = {
    val objective = state.goals(goalIndex)
    val hypothesis = objective.hypotheses(hypothesisIndex)
    hypothesis match {
      case ConnectorFormula(`Or`, Seq(a, b)) => Some(TacticResult(ProofStateDiff(goalIndex, IndexedSeq(
        ProofGoalUpdateHypothesis(hypothesisIndex, IndexedSeq(a)),
        ProofGoalUpdateHypothesis(hypothesisIndex, IndexedSeq(b)),
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
  proofState.goals.zipWithIndex.map { case (goal, i) =>
    Seq(s"goal #$i:", prettyProofGoal(goal)).mkString("\n")
  }.mkString("\n\n")
}

def replaceInArray[T](array: IndexedSeq[T], i: Int, replacement: IndexedSeq[T]): IndexedSeq[T] =
  array.take(i) ++ replacement ++ array.drop(i + 1)

def mutateState(state: ProofState, tacticResult: TacticResult): ProofState = {
  val diff = tacticResult.diff
  val goal = state.goals(diff.goalIndex)
  val added = diff.replacement.map {
    case ProofGoalUpdateGoal(newGoal, newHypotheses) =>
      ProofGoal(replaceInArray(goal.hypotheses, 0, newHypotheses), newGoal)
    case ProofGoalUpdateHypothesis(hypothesisIndex, newHypotheses) =>
      goal.copy(hypotheses = replaceInArray(goal.hypotheses, hypothesisIndex, newHypotheses))
  }
  ProofState(replaceInArray(state.goals, diff.goalIndex, added))
}

def proofGoalToSequent(proofGoal: ProofGoal): Sequent = Sequent(proofGoal.hypotheses.toSet, Set(proofGoal.goal))
def formulaToSequent(formula: Formula): Sequent = Sequent(Set.empty, Set(formula))
def formulaToProofState(formula: Formula): ProofState = ProofState(IndexedSeq(ProofGoal(IndexedSeq.empty, formula)))

// translation: id -> proof_step
def iterate(nextId: Int, state: ProofState, seq: Seq[Tactic], proof: SCProofBuilder, shadow: IndexedSeq[Int], translation: Map[Int, Int]): (SCProofBuilder, Map[Int, Int]) = {
  seq match {
    case tactic +: t =>
      val result = tactic(state).get
      val newState = mutateState(state, result)
      val updatedGoalIndex = result.diff.goalIndex
      val id = shadow(updatedGoalIndex)
      val replacementIds = result.diff.replacement.indices.map(_ + nextId)
      val newShadow = replaceInArray(shadow, updatedGoalIndex, replacementIds)
      val newNextId = nextId + result.diff.replacement.size
      val (recursiveProof, recursiveTranslation) = iterate(newNextId, newState, t, proof, newShadow, translation)
      val stepIndex = recursiveProof.steps.size
      val premises = replacementIds.map(recursiveTranslation)
      val majorStep = SCAnyProofStep(proofGoalToSequent(state.goals(updatedGoalIndex)), premises, Seq.empty)
      val newProofWithNewStep = recursiveProof.withNewSteps(majorStep)
      (newProofWithNewStep, recursiveTranslation + (id -> (newProofWithNewStep.steps.size - 1)))
    case _ =>
      (proof, translation)
  }
}

def reconstructProof(conclusion: Formula, seq: Seq[Tactic]): SCProofBuilder =
  iterate(1, formulaToProofState(conclusion), seq, SCProofBuilder(), IndexedSeq(0), Map.empty)._1


@main def tests: Unit = {
  def variable(name: String): Formula = PredicateFormula(SchematicPredicateLabel(name, 0), Seq())

  val (a, b, c) = (variable("a"), variable("b"), variable("c"))

  // ---

  val conclusion: Formula = (a /\ b) ==> a
  val steps: IndexedSeq[Tactic] = IndexedSeq(
    TacticAssume(0),
    TacticDestructHypothesis(0, 0),
    TacticWeakenHypothesis(0, 1),
    TacticEliminate(0),
  )

  val builder = reconstructProof(conclusion, steps)

  builder.steps.map(s => s"${Printer.prettySequent(s.conclusion)} by ${s.premises.mkString(", ")}").foreach(println)
  println()

  val scproof = builder.build

  println(Printer.prettySCProof(scproof))

  assert(SCProofChecker.checkSCProof(scproof)._1)

  println()
  println("The proof is valid.")
}
