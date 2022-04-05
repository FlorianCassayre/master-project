package me.cassayre.florian.masterproject.legacy.meta

import lisa.kernel.Printer
import lisa.kernel.proof.{SCProof, SCProofChecker, SequentCalculus}
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.legacy.parser.SCReader.*
import me.cassayre.florian.masterproject.front.unification.Unifier
import me.cassayre.florian.masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.{Cut, Hypothesis, LeftAnd, RightAnd, SCProofStep, SCSubproof, Weakening}
import me.cassayre.florian.masterproject.util.SCUtils
import proven.tactics.SimplePropositionalSolver

object Meta {

  case class Sequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula])
  def sequentToKernel(sequent: Sequent): lisa.kernel.proof.SequentCalculus.Sequent =
    lisa.kernel.proof.SequentCalculus.Sequent(sequent.left.map(toKernel).toSet, sequent.right.map(toKernel).toSet)
  given Conversion[Sequent, lisa.kernel.proof.SequentCalculus.Sequent] = sequentToKernel

  //

  sealed abstract class MetaLogical
  case class MetaRule(hypotheses: IndexedSeq[MetaLogical], conclusion: MetaLogical) extends MetaLogical
  case class MetaSequent(sequent: Sequent) extends MetaLogical

  given Conversion[Sequent, MetaSequent] = MetaSequent.apply
  given Conversion[MetaSequent, Sequent] = _.sequent

  case class ProofState(goals: IndexedSeq[MetaLogical])

  sealed abstract class MetaSelector
  case class MetaRuleSelector(hypotheses: IndexedSeq[(Int, MetaSelector)], conclusion: MetaSelector) extends MetaSelector
  case class MetaSequentSelector(left: IndexedSeq[Int], right: IndexedSeq[Int]) extends MetaSelector

  case class Args(
    selector: Option[MetaSelector] = None,
    conservative: Boolean = false,
    functions: Map[SchematicFunctionLabel[?], (Formula, Seq[VariableTerm])] = Map.empty,
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableTerm])] = Map.empty,
    //connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])] = Map.empty,
  ) {
    def withNullaryPredicates(predicates: (SchematicPredicateLabel[0], Formula)*): Args =
      copy(predicates = this.predicates ++ predicates.map { case (sp, f) => sp -> (f, Seq.empty) }.toMap)
  }

  def prepareMetaUnification(pattern: MetaLogical, value: MetaLogical, args: Args): Option[(Seq[(Formula, Formula)], MetaSelector)] = {
    args.selector.flatMap { selector =>
      def recursive(selector: MetaSelector, pattern: MetaLogical, value: MetaLogical): Option[Seq[(Formula, Formula)]] = (selector, pattern, value) match {
        case (MetaRuleSelector(il, ir), MetaRule(pl, pr), MetaRule(vl, vr)) =>
          lazy val arityCorrect = il.sizeIs == pl.size
          lazy val indicesCorrect = il.map(_._1).forall(vl.indices.contains)
          if(arityCorrect && indicesCorrect) {
            val options = il.zip(pl).map { case ((i, childArgs), childPattern) => recursive(childArgs, childPattern, vl(i)) } :+
              recursive(ir, pr, vr)
            val values = options.collect { case Some(v) => v }
            if(options.sizeIs == values.size) {
              Some(values.flatten)
            } else {
              None
            }
          } else {
            None
          }
        case (MetaSequentSelector(sl, sr), MetaSequent(fp), MetaSequent(fv)) =>
          lazy val arityCorrect = sl.sizeIs == fp.left.size && sr.sizeIs == fp.right.size
          lazy val indicesCorrect = sl.forall(fv.left.indices.contains) && sr.forall(fv.right.indices.contains)
          if(arityCorrect && indicesCorrect) {
            val pairs = sl.zip(fp.left).map { case (i, childPattern) => (childPattern, fv.left(i)) } ++
              sr.zip(fp.right).map { case (i, childPattern) => (childPattern, fv.right(i)) }
            Some(pairs)
          } else {
            None
          }
        case _ => None
      }

      recursive(selector, pattern, value).map(_ -> selector)
    }
  }

  def canApplyRuleBackward(rule: MetaRule, goal: MetaLogical, args: Args): Boolean = {
    prepareMetaUnification(rule.conclusion, goal, args) match {
      case Some(value) =>
        val (left, right) = value._1.unzip
        Unifier.unifyAllFormulas(left, right) match {
          case Unifier.UnificationSuccess(ctx) => true
          case Unifier.UnificationFailure(message) => false
        }
      case None => false
    }
  }

  //

  val (p, q, r, s) = (
    SchematicPredicateLabel[0]("p"),
    SchematicPredicateLabel[0]("q"),
    SchematicPredicateLabel[0]("r"),
    SchematicPredicateLabel[0]("s"),
  )

  val impI = MetaRule(
    IndexedSeq(
      MetaRule(
        IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(p))),
        Sequent(IndexedSeq.empty, IndexedSeq(q)),
      )
    ),
    Sequent(IndexedSeq.empty, IndexedSeq(p ==> q)),
  )
  val disjE = MetaRule(
    IndexedSeq(
      Sequent(IndexedSeq.empty, IndexedSeq(p \/ q)),
      MetaRule(
        IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(p))),
        Sequent(IndexedSeq.empty, IndexedSeq(r)),
      ),
      MetaRule(
        IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(q))),
        Sequent(IndexedSeq.empty, IndexedSeq(r)),
      ),
    ),
    Sequent(IndexedSeq.empty, IndexedSeq(r)),
  )

  sealed abstract class ReconstructResult
  case class ReconstructedSteps(steps: Sequent => IndexedSeq[SCProofStep]) extends ReconstructResult
  case class ReconstructedFunction(f: PartialFunction[IndexedSeq[ReconstructResult], ReconstructResult]) extends ReconstructResult

  sealed abstract class Tactic {
    def applyBackward(goal: MetaLogical, args: Args): Option[AppliedTactic]
  }
  // (conclusion, reconstructed_hypotheses_steps) => reconstructed_steps
  type Reconstruct = PartialFunction[(MetaLogical, IndexedSeq[ReconstructResult]), ReconstructResult]
  case class AppliedTactic(
    partialConclusion: MetaLogical, // /!\ Partial meta sequent
    partialHypotheses: IndexedSeq[MetaLogical], // Same here
    selected: MetaSelector,
    reconstruct: Reconstruct,
  )

  case object SolverTactic extends Tactic {
    override def applyBackward(goal: MetaLogical, args: Args): Option[AppliedTactic] = {
      goal match {
        case _: MetaRule => None
        case MetaSequent(sequent) =>
          // TODO fix the solver to return an option
          // TODO check empty arguments
          val proof = SimplePropositionalSolver.solveSequent(sequent)
          Some(AppliedTactic(
            goal,
            IndexedSeq.empty,
            MetaSequentSelector(sequent.left.indices, sequent.right.indices), // Does not really matter
            (_, _) => ReconstructedSteps(bot => proof.steps), // TODO weaken?
          ))
      }
    }
  }

  sealed abstract class PredefRule extends Tactic {
    def rule: MetaRule
    def reconstruct: UnificationContext => Reconstruct
    override final def applyBackward(goal: MetaLogical, args: Args): Option[AppliedTactic] = {
      val option = prepareMetaUnification(rule.conclusion, goal, args) match {
        case Some((value, selector)) =>
          val (left, right) = value.unzip
          Unifier.unifyAllFormulas(left, right) match {
            case Unifier.UnificationSuccess(ctx) => Some((ctx, selector))
            case Unifier.UnificationFailure(message) => None
          }
        case None => None
      }

      option.map { case (ctx, selector) =>
        def instantiateMeta(meta: MetaLogical): MetaLogical = meta match {
          case MetaRule(hypotheses, conclusion) =>
            MetaRule(
              hypotheses.map(instantiateMeta),
              instantiateMeta(conclusion),
            )
          case MetaSequent(sequent) => MetaSequent(Sequent(
            sequent.left.map(instantiateFormulaFromContext(_, ctx)),
            sequent.right.map(instantiateFormulaFromContext(_, ctx)),
          ))
        }

        AppliedTactic(
          instantiateMeta(rule.conclusion),
          rule.hypotheses.map(instantiateMeta),
          selector,
          reconstruct(ctx)
        )
      }
    }
  }

  case object RuleHypothesis extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq.empty,
      Sequent(IndexedSeq(p), IndexedSeq(p)),
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq()) =>
        ReconstructedSteps(bot => IndexedSeq(
          Hypothesis(bot, ctx(p))
        ))
    }
  }

  case object RuleIntroductionLeftAnd extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq(
        Sequent(IndexedSeq(p, q), IndexedSeq.empty),
      ),
      Sequent(IndexedSeq(p /\ q), IndexedSeq.empty),
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq(ReconstructedSteps(seqPQ))) =>
        ReconstructedSteps(bot => IndexedSeq(
          LeftAnd(bot, -1, ctx(p), ctx(q))
        ))
    }
  }

  case object RuleIntroductionRightAnd extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq(
        Sequent(IndexedSeq.empty, IndexedSeq(p)),
        Sequent(IndexedSeq.empty, IndexedSeq(q)),
      ),
      Sequent(IndexedSeq.empty, IndexedSeq(p /\ q)),
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq(ReconstructedSteps(seqPF), ReconstructedSteps(seqQF))) =>
        ReconstructedSteps(bot => IndexedSeq(
          RightAnd(bot, Seq(-1, -2), Seq(ctx(p), ctx(q)))
        ))
    }
  }

  case object RuleIntroductionMeta extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq(
        Sequent(IndexedSeq(p), IndexedSeq(q)),
      ),
      MetaRule(
        IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(p))),
        Sequent(IndexedSeq.empty, IndexedSeq(q)),
      )
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq(ReconstructedSteps(_))) =>
        ReconstructedFunction({
          case IndexedSeq(ReconstructedSteps(spSteps)) =>
            ReconstructedSteps(
              bot => // |- q
                IndexedSeq(
                  Weakening(bot.copy(right = bot.right :+ ctx(p)), -1), // Is weakening required?
                  SCSubproof(SCProof(spSteps(bot.copy(left = bot.left :+ ctx(p)))), Seq.empty),
                  Cut(bot, 1, 0, ctx(p)),
                )
            )
        })
    }
  }

  case object RuleEliminationMeta extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq(
        MetaRule(
          IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(p))),
          Sequent(IndexedSeq.empty, IndexedSeq(q)),
        ),
      ),
      Sequent(IndexedSeq(p), IndexedSeq(q)),
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq(ReconstructedFunction(f))) =>
        ReconstructedSteps(bot => IndexedSeq( // p |- q
          ???
        ))
    }
  }

  case object RuleEliminationRightOr extends PredefRule {
    def rule: MetaRule = MetaRule(
      IndexedSeq(
        MetaSequent(Sequent(IndexedSeq.empty, IndexedSeq(p \/ q))),
        MetaRule(
          IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(p))),
          Sequent(IndexedSeq.empty, IndexedSeq(r)),
        ),
        MetaRule(
          IndexedSeq(Sequent(IndexedSeq.empty, IndexedSeq(q))),
          Sequent(IndexedSeq.empty, IndexedSeq(r)),
        ),
      ),
      Sequent(IndexedSeq.empty, IndexedSeq(r)),
    )
    override def reconstruct: UnificationContext => Reconstruct = ctx => {
      case (_, IndexedSeq(ReconstructedFunction(f))) =>
        ReconstructedSteps(bot => IndexedSeq( // p |- q
          ???
        ))
    }
  }

  sealed abstract class ProofStateMutator
  case class MutateProofGoal(tactic: Tactic, arguments: Args) extends ProofStateMutator
  case class SelectProofGoal(goalId: Int) extends ProofStateMutator

  case class ProofStateSnapshot(
    proofState: ProofState,
    shadowProofState: IndexedSeq[Int],
    nextId: Int,
  )

  case class ProofModeState(
    // In reverse direction (meaning the last element is the initial state)
    steps: Seq[(ProofStateSnapshot, Option[AppliedTactic])],
  ) {
    require(steps.nonEmpty)
    def lastSnapshot: ProofStateSnapshot = steps.head._1
    def initialSnapshot: ProofStateSnapshot = steps.last._1
    def withNewStep(newSnapshot: ProofStateSnapshot, newTactic: AppliedTactic): ProofModeState =
      ProofModeState((newSnapshot, Some(newTactic)) +: steps)
    def withNewStep(newSnapshot: ProofStateSnapshot): ProofModeState =
      ProofModeState((newSnapshot, None) +: steps)
  }

  def mutateProofMode(proofModeState: ProofModeState, mutator: ProofStateMutator): Option[ProofModeState] = mutator match {
    case MutateProofGoal(tactic, arguments) =>
      val snapshot = proofModeState.lastSnapshot
      snapshot.proofState.goals match {
        case goal +: untouchedGoals =>
          tactic.applyBackward(goal, arguments).map { appliedTactic =>
            // New goals are inserted at the beginning, in the same order
            val nHypotheses = appliedTactic.partialHypotheses.size
            val filledHypotheses = goal match {
              case _: MetaRule => appliedTactic.partialHypotheses
              case MetaSequent(sequent) => appliedTactic.partialHypotheses.map {
                case rule: MetaRule => rule
                case MetaSequent(sequentPartial) =>
                  // Only fill concrete sequents
                  def fillSide(goalSide: IndexedSeq[Formula], partialSide: IndexedSeq[Formula], argumentsSide: Seq[Int]): IndexedSeq[Formula] = {
                    val template =
                      if(arguments.conservative) {
                        goalSide
                      } else {
                        val argumentsSideSet = argumentsSide.toSet
                        goalSide.zipWithIndex.collect { case (f, i) if !argumentsSideSet.contains(i) => f }
                      }
                    partialSide ++ template
                  }
                  val selector = appliedTactic.selected.asInstanceOf[MetaSequentSelector]
                  val left = fillSide(sequent.left, sequentPartial.left, selector.left)
                  val right = fillSide(sequent.right, sequentPartial.right, selector.right)
                  MetaSequent(Sequent(left, right))
              }
            }
            val newSnapshot = ProofStateSnapshot(
              ProofState(filledHypotheses ++ untouchedGoals),
              (snapshot.nextId until (snapshot.nextId + nHypotheses)) ++ snapshot.shadowProofState.tail,
              snapshot.nextId + nHypotheses,
            )
            proofModeState.withNewStep(newSnapshot, appliedTactic)
          }
        case _ => None
      }
    case SelectProofGoal(goalId) =>
      val snapshot = proofModeState.lastSnapshot
      if(snapshot.proofState.goals.indices.contains(goalId)) {
        def withSelected[T](seq: IndexedSeq[T]): IndexedSeq[T] =
          (seq(goalId) +: seq.take(goalId)) ++ seq.drop(goalId + 1)
        Some(proofModeState.withNewStep(
          snapshot.copy(
            proofState = ProofState(withSelected(snapshot.proofState.goals)),
            shadowProofState = withSelected(snapshot.shadowProofState),
          ),
        ))
      } else {
        None
      }
  }

  def reconstructSCProof(proofModeState: ProofModeState): SCProof = {
    proofModeState.initialSnapshot match {
      case ProofStateSnapshot(ProofState(IndexedSeq(MetaSequent(conclusionSequent))), IndexedSeq(conclusionId), _) =>
        if(proofModeState.lastSnapshot.proofState.goals.isEmpty) {
          val allData = proofModeState.steps.zip(proofModeState.steps.tail).foldLeft(Map.empty[Int, (ReconstructResult, Seq[Int], MetaLogical, IndexedSeq[Int])]) {
            case (data, ((topSnapshot, appliedTacticOption), (bottomSnapshot, _))) =>
              appliedTacticOption match {
                case Some(appliedTactic) =>
                  val id = bottomSnapshot.shadowProofState.head
                  val hypothesesIds = topSnapshot.shadowProofState.take(appliedTactic.partialHypotheses.size)

                  val reconstructedBlueprint = appliedTactic.reconstruct(appliedTactic.partialConclusion, topSnapshot.shadowProofState.map(i => data(i)._1))

                  data + (id -> (
                    reconstructedBlueprint,
                    hypothesesIds,
                    bottomSnapshot.proofState.goals.head,
                    topSnapshot.shadowProofState,
                  ))
                case None => data // Rewrite at the meta level = Nothing to do
              }
          }

          // Invariant: each dependency has a larger id than its parent
          // Therefore a topological ordering is obtained simply by sorting the ids
          val order = allData.keySet.toSeq.sorted.reverse
          val (finalProof, _) = order.foldLeft((SCProof(), Map.empty[Int, Int])) { case ((proof, translation), id) =>
            // translation: Map[id -> sc_step_absolute_index]
            val (fragment, dependencies, bottoms, shadowGoals) = allData(id)
            fragment match {
              case ReconstructedSteps(stepsF) =>
                val bottomSequent = bottoms.asInstanceOf[MetaSequent].sequent
                val stepsRaw = stepsF(bottomSequent)
                val stepsAppendable = stepsRaw.zipWithIndex.map { case (step, stepRelativeIndex) =>
                  def premiseMapping(p: Int): Int = {
                    if(p < 0) {
                      val i = -p - 1
                      assert(i < shadowGoals.size)
                      val selectedGoalId = shadowGoals(i)
                      assert(fragment match {
                        case _: ReconstructedSteps => true
                        case _: ReconstructedFunction => false
                      })
                      translation(selectedGoalId)
                    } else {
                      assert(p < stepRelativeIndex)
                      proof.steps.size + p
                    }
                  }
                  SCUtils.mapPremises(step, premiseMapping)
                }
                val newProof = proof.withNewSteps(stepsAppendable)
                val lastStepIndex = newProof.steps.size - 1

                (newProof, translation + (id -> lastStepIndex))
              case ReconstructedFunction(f) => (proof, translation) // Functions cannot be reconstructed (they should be applied)
            }
          }

          finalProof
        } else {
          // TODO we could still support imports (if they are all sequents)
          throw new UnsupportedOperationException("Cannot reconstruct a proof that relies on hypotheses")
        }
      case _ =>
        throw new UnsupportedOperationException("Cannot reconstruct a proof with several conclusions, or for which the conclusion is not a sequent")
    }
  }

  def initialProofModeState(goals: MetaLogical*): ProofModeState =
    ProofModeState(Seq((ProofStateSnapshot(ProofState(goals.toIndexedSeq), goals.indices, goals.size), None)))


  // Dirty
  def prettyMetaLogical(meta: MetaLogical): String = {
    def removeSchematicConnectors(formula: Formula): Formula = formula match {
      case _: PredicateFormula => formula
      case ConnectorFormula(label: SchematicConnectorLabel[?], _) =>
        ConnectorFormula(ConstantConnectorLabel("?", 0), Seq.empty)
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(removeSchematicConnectors))
      case BinderFormula(label, bound, inner) => BinderFormula(label, bound, removeSchematicConnectors(inner))
    }
    def removeSchematicConnectorsSequent(sequent: Sequent): Sequent =
      Sequent(sequent.left.map(removeSchematicConnectors), sequent.right.map(removeSchematicConnectors))
    meta match {
      case MetaRule(hypotheses, conclusion) =>
        val hypothesesStr = hypotheses.map(prettyMetaLogical).mkString("; ")
        val conclusionStr = prettyMetaLogical(conclusion)
        s"($hypothesesStr) |= $conclusionStr"
      case MetaSequent(sequent) => Printer.prettySequent(sequentToKernel(removeSchematicConnectorsSequent(sequent)))
    }
  }

  // === Tests ===

  @main def testMeta(): Unit = {
    val (a, b, c, d) = (
      PredicateFormula(ConstantPredicateLabel[0]("a"), Seq.empty),
      PredicateFormula(ConstantPredicateLabel[0]("b"), Seq.empty),
      PredicateFormula(ConstantPredicateLabel[0]("c"), Seq.empty),
      PredicateFormula(ConstantPredicateLabel[0]("d"), Seq.empty)
    )

    val (initial, steps) = {
      val sequentToProve: Sequent =
        Sequent(IndexedSeq(a), IndexedSeq(a))
      val backwardProofSteps: Seq[ProofStateMutator] =
        Seq(
          MutateProofGoal(RuleEliminationRightOr, Args(Some(MetaSequentSelector(IndexedSeq.empty, IndexedSeq(0))),
            predicates = Map(p -> (a, Seq.empty), q -> (a, Seq.empty))
          )),
          //MutateProofGoal(SolverTactic, Args()),
          //MutateProofGoal(RuleIntroductionLeftAnd, Args(Some(MetaSequentSelector(IndexedSeq(0), IndexedSeq.empty)))),
          //MutateProofGoal(RuleHypothesis, Args(Some(MetaSequentSelector(IndexedSeq(0), IndexedSeq(0))))),
        )

      (initialProofModeState(MetaSequent(sequentToProve)), backwardProofSteps)
    }

    val finalProofMode = steps.foldLeft(initial)((mode, mutator) => mutateProofMode(mode, mutator).get)

    println(finalProofMode.lastSnapshot.proofState.goals.map(prettyMetaLogical).mkString("\n"))
    println()

    assert(finalProofMode.lastSnapshot.proofState.goals.isEmpty, "The proof state has unproven goals")
    val scProof = reconstructSCProof(finalProofMode)
    println(Printer.prettySCProof(scProof))
    assert(SCProofChecker.checkSCProof(scProof).isValid)
  }

}
