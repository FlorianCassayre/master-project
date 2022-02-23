package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.Printer.*
import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.proof.SCProof

case class ProofState(premises: IndexedSeq[Formula], goals: IndexedSeq[Formula]) {
  def mutate(diff: ProofStateDiff): ProofState = {
    def applyTransformation(sequence: IndexedSeq[Formula], transform: Map[Option[Int], Seq[Formula]]): IndexedSeq[Formula] = {
      transform.getOrElse(None, Seq.empty).toIndexedSeq ++ sequence.map(Seq.apply(_)).zipWithIndex.flatMap { case (formula, i) => transform.get(Some(i)) match {
        case Some(by) => by
        case None => formula
      }}
    }
    ProofState(applyTransformation(premises, diff.premises), applyTransformation(goals, diff.goals))
  }
}
object ProofState {
  def apply(premises: IndexedSeq[Formula] = IndexedSeq.empty, goals: IndexedSeq[Formula] = IndexedSeq.empty): ProofState =
    new ProofState(premises, goals)
}

def prettyProofState(state: ProofState): String = {
  val premisesStr = state.premises.map(Printer.prettyFormula(_))
  val goalsStr = state.goals.map(Printer.prettyFormula(_))
  val maxLength = (premisesStr ++ goalsStr).map(_.length).maxOption.getOrElse(1)
  (premisesStr ++ Seq("=" * maxLength) ++ goalsStr).mkString("\n")
}

case class ProofStateDiff(premises: Map[Option[Int], Seq[Formula]], goals: Map[Option[Int], Seq[Formula]])
object ProofStateDiff {
  def apply(premises: Map[Option[Int], Seq[Formula]] = Map.empty, goals: Map[Option[Int], Seq[Formula]] = Map.empty): ProofStateDiff =
    new ProofStateDiff(premises, goals)
  def empty: ProofStateDiff = ProofStateDiff()
}

sealed abstract class ProofStateSelector

case class SelectorSinglePremise(premiseIndex: Int = 0) extends ProofStateSelector
case class SelectorSingleGoal(goalIndex: Int = 0) extends ProofStateSelector


abstract class Tactic {
  type T
  def apply(state: ProofState): Option[T]
  def toDiff(parameters: T): ProofStateDiff
}

case class TacticAssume(selector: SelectorSingleGoal) extends Tactic {
  override type T = (Formula, Formula)
  override def apply(state: ProofState): Option[T] = {
    val goal = state.goals(selector.goalIndex) // TODO check index out of bounds
    state.goals(selector.goalIndex) match {
      case ConnectorFormula(`Implies`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }
  def toDiff(parameters: T): ProofStateDiff = {
    val (a, b) = parameters
    ProofStateDiff(
      premises = Map(None -> Seq(a)),
      goals = Map(Some(selector.goalIndex) -> Seq(b))
    )
  }
}

case class TacticEliminate(goalSelector: SelectorSingleGoal, premiseSelector: SelectorSinglePremise) extends Tactic {
  override type T = (Formula, Formula)
  override def apply(state: ProofState): Option[T] = {
    val goal = state.goals(goalSelector.goalIndex)
    val premise = state.premises(premiseSelector.premiseIndex)
    if(goal == premise) {
      Some((goal, premise))
    } else {
      None
    }
  }
  def toDiff(parameters: T): ProofStateDiff = {
    val (a, b) = parameters
    ProofStateDiff(
      goals = Map(Some(goalSelector.goalIndex) -> Seq.empty)
    )
  }
}

case class TacticDestruct(selector: SelectorSingleGoal | SelectorSinglePremise) extends Tactic {
  override type T = (Formula, Formula)
  override def apply(state: ProofState): Option[T] = {
    val formula = selector match {
      case SelectorSingleGoal(goalIndex) => state.goals(goalIndex)
      case SelectorSinglePremise(premiseIndex) => state.premises(premiseIndex)
    }
    formula match {
      case ConnectorFormula(`And`, args) if args.sizeIs >= 2 => Some((args.head, if(args.sizeIs > 2) ConnectorFormula(And, args.tail) else args.tail.head))
      case _ => None
    }
  }
  def toDiff(parameters: T): ProofStateDiff = {
    val (a, b) = parameters
    selector match {
      case SelectorSingleGoal(goalIndex) => ProofStateDiff(goals = Map(Some(goalIndex) -> Seq(a, b)))
      case SelectorSinglePremise(premiseIndex) => ProofStateDiff(premises = Map(Some(premiseIndex) -> Seq(a, b)))
    }
  }
}

case class HighLevelProof(proposition: Formula, steps: Seq[Tactic])

def applyTactics(state: ProofState, tactics: Seq[Tactic]): Option[ProofState] = {
  tactics match {
    case tactic +: remainingTactics =>
      tactic(state) match {
        case Some(parameters) =>
          val diff = tactic.toDiff(parameters)
          applyTactics(state.mutate(diff), remainingTactics)
        case None => None // Failure
      }
    case _ => Some(state)
  }
}
def applyTactics(hlp: HighLevelProof): Option[ProofState] = applyTactics(ProofState(goals = IndexedSeq(hlp.proposition)), hlp.steps)

def checkHighLevelProof(hlp: HighLevelProof): Boolean = applyTactics(hlp).exists(_.goals.isEmpty)


@main def tests(): Unit = {
  def variable(name: String): Formula = PredicateFormula(SchematicPredicateLabel(name, 0), Seq())

  val (a, b, c) = (variable("a"), variable("b"), variable("c"))

  val hlp = HighLevelProof(
    a ==> ((b /\ c) ==> (c /\ a)),
    Seq(
      TacticAssume(SelectorSingleGoal()),
      TacticAssume(SelectorSingleGoal()),
      TacticDestruct(SelectorSingleGoal()),
      TacticDestruct(SelectorSinglePremise()),
      TacticEliminate(SelectorSingleGoal(), SelectorSinglePremise(1)),
      TacticEliminate(SelectorSingleGoal(), SelectorSinglePremise(2)),
    )
  )

  println(prettyProofState(applyTactics(hlp).get))

  assert(checkHighLevelProof(hlp))
}
