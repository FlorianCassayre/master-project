package masterproject.front

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import masterproject.SCUtils
import masterproject.front.Unification.*
import proven.tactics.SimplePropositionalSolver

object Front {

  object Notations {
    val (la, lb, lc) = (SchematicPredicateLabel("a", 0), SchematicPredicateLabel("b", 0), SchematicPredicateLabel("c", 0))
    val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))
  }

  def prettySequent(left: Seq[Formula], right: Seq[Formula], partial: Boolean = false): String = { // TODO this should be handled by the printer...
    def prettySequence(seq: Seq[Formula], leftSide: Boolean): String = {
      val strs = seq.map(Printer.prettyFormula(_))
      val rest = "..."
      val strs1 = if(partial) (if(leftSide) rest +: strs else strs :+ rest) else strs
      strs1.mkString("; ")
    }

    s"${prettySequence(left, true)} ⊢ ${prettySequence(right, false)}"
  }

  case class ProofGoal(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) {
    override def toString: String = prettySequent(left, right)
  }

  case class ProofState(goals: IndexedSeq[ProofGoal]) {
    override def toString: String =
      ((if (goals.nonEmpty) s"${goals.size} goal${if (goals.sizeIs > 1) "s" else ""}" else "[zero goals]") +:
          goals.map(_.toString)
        ).mkString("\n")
  }

  case class PartialProofGoal(left: IndexedSeq[Formula], right: IndexedSeq[Formula])

  sealed abstract class Rule {
    def hypotheses: IndexedSeq[PartialProofGoal]
    def conclusion: PartialProofGoal

    require(hypotheses.forall(isPartialProofGoalWellFormed))
    require(isPartialProofGoalWellFormed(conclusion))

    // The premises indexing is implicit:
    // * 0, 1, 2 will reference respectively the first, second and third steps in that array
    // * -1, -2, -3 will reference respectively the first second and third premises, as returned by `hypotheses`
    def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep]

    override def toString: String = {
      def prettyPartialProofGoal(partialProofGoal: PartialProofGoal): String =
        prettySequent(partialProofGoal.left, partialProofGoal.right, true)

      val top = hypotheses.map(prettyPartialProofGoal).mkString(" " * 6)
      val bottom = prettyPartialProofGoal(conclusion)
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

  sealed trait RuleSolver extends Rule {
    override final def hypotheses: IndexedSeq[PartialProofGoal] = IndexedSeq.empty
    override final def conclusion: PartialProofGoal = PartialProofGoal(IndexedSeq.empty, IndexedSeq.empty)
  }

  case object RulePropositionalSolver extends RuleSolver {
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] = {
      val proof = SimplePropositionalSolver.solveSequent(bot)
      assert(proof.imports.isEmpty)
      IndexedSeq(SCSubproof(proof))
    }
  }

  sealed trait RuleIntroduction extends Rule

  case object RuleIntroductionLeftAnd extends RuleIntroduction {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialProofGoal] =
      IndexedSeq(PartialProofGoal(IndexedSeq(a, b), IndexedSeq.empty))
    override def conclusion: PartialProofGoal =
      PartialProofGoal(IndexedSeq(a /\ b), IndexedSeq.empty)
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(LeftAnd(bot, -1, ctx.predicates(la), ctx.predicates(lb)))
  }

  case object RuleIntroductionRightAnd extends RuleIntroduction {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialProofGoal] =
      IndexedSeq(
        PartialProofGoal(IndexedSeq.empty, IndexedSeq(a)),
        PartialProofGoal(IndexedSeq.empty, IndexedSeq(b)),
      )
    override def conclusion: PartialProofGoal =
      PartialProofGoal(IndexedSeq.empty, IndexedSeq(a /\ b))
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(RightAnd(bot, Seq(-1, -2), Seq(ctx.predicates(la), ctx.predicates(lb))))
  }

  //

  sealed trait RuleElimination extends Rule

  case object RuleEliminationLeftAnd extends RuleElimination {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialProofGoal] =
      IndexedSeq(PartialProofGoal(IndexedSeq(a /\ b), IndexedSeq.empty))
    override def conclusion: PartialProofGoal =
      PartialProofGoal(IndexedSeq(a, b), IndexedSeq.empty)
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(
        Hypothesis(bot +> ctx.predicates(la), ctx.predicates(la)),
        Hypothesis(bot +> ctx.predicates(lb), ctx.predicates(lb)),
        RightAnd(bot +> (ctx.predicates(la) /\ ctx.predicates(lb)), Seq(0, 1), Seq(ctx.predicates(la), ctx.predicates(lb))),
        Cut(bot, 2, -1, ctx.predicates(la) /\ ctx.predicates(lb)),
      )
  }

  //sealed trait Simplification extends Rule

  // TODO add other parameters, such as formulas or terms
  case class RuleApplication(rule: Rule, formulas: Option[(IndexedSeq[Int], IndexedSeq[Int])] = None)


  // Functions and algorithms

  case class Scope(boundVariables: Set[VariableLabel] = Set.empty)

  def isTermWellFormed(term: Term)(implicit ctx: Scope = Scope()): Boolean = term match {
    case VariableTerm(label) => ctx.boundVariables.contains(label) // Free variables are forbidden, use schemas
    case FunctionTerm(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isTermWellFormed)
  }

  def isFormulaWellFormed(formula: Formula)(implicit ctx: Scope = Scope()): Boolean = formula match {
    case PredicateFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isTermWellFormed(_))
    case ConnectorFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isFormulaWellFormed(_))
    case BinderFormula(label, bound, inner) =>
      !ctx.boundVariables.contains(bound) && isFormulaWellFormed(inner)(ctx.copy(boundVariables = ctx.boundVariables + bound))
  }

  def isProofGoalWellFormed(proofGoal: ProofGoal): Boolean =
    proofGoal.left.forall(isFormulaWellFormed) && proofGoal.right.forall(isFormulaWellFormed)

  def isPartialProofGoalWellFormed(partialProofGoal: PartialProofGoal): Boolean =
    partialProofGoal.left.forall(isFormulaWellFormed) && partialProofGoal.right.forall(isFormulaWellFormed)

  //

  // Assumes that all the schematic predicates in the map are of arity zero
  def simultaneousNullaryPredicateSchemaInstantiation(phi: Formula, map: Map[SchematicPredicateLabel, Formula]): Formula = phi match {
    case PredicateFormula(label, args) =>
      label match {
        case _: ConstantPredicateLabel => phi
        case schematic: SchematicPredicateLabel =>
          map.get(schematic) match {
            case Some(value) => value
            case None => phi
          }
      }
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(simultaneousNullaryPredicateSchemaInstantiation(_, map)))
    case BinderFormula(label, bound, inner) => BinderFormula(label, bound, simultaneousNullaryPredicateSchemaInstantiation(inner, map))
  }

  def simultaneousNullaryFunctionSchemaInstantiation(term: Term, map: Map[SchematicFunctionLabel, Term]): Term = term match {
    case variable: VariableTerm => variable
    case FunctionTerm(label, args) =>
      val optional = label match {
        case _: ConstantFunctionLabel => None
        case schematic: SchematicFunctionLabel => map.get(schematic)
      }
      optional match {
        case Some(value) => value
        case None => FunctionTerm(label, args.map(simultaneousNullaryFunctionSchemaInstantiation(_, map)))
      }
  }

  def simultaneousNullaryFunctionSchemaInstantiation(phi: Formula, map: Map[SchematicFunctionLabel, Term]): Formula = phi match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(simultaneousNullaryFunctionSchemaInstantiation(_, map)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(simultaneousNullaryFunctionSchemaInstantiation(_, map)))
    case BinderFormula(label, bound, inner) => BinderFormula(label, bound, simultaneousNullaryFunctionSchemaInstantiation(inner, map))
  }

  def mutateProofGoal(proofGoal: ProofGoal, application: RuleApplication): Option[(IndexedSeq[ProofGoal], UnificationContext)] = {
    val conclusion = application.rule.conclusion

    def parametersOption: Option[(IndexedSeq[Int], IndexedSeq[Int])] = application.formulas match {
      case Some(pair @ (explicitLeft, explicitRight)) =>
        require(conclusion.left.size == explicitLeft.size)
        require(conclusion.right.size == explicitRight.size)
        Some(pair)
      case None =>
        def iterator = for {
          leftIndices <- proofGoal.left.indices.combinations(conclusion.left.size).flatMap(_.permutations)
          rightIndices <- proofGoal.right.indices.combinations(conclusion.right.size).flatMap(_.permutations)
        } yield (leftIndices, rightIndices)
        val seq = iterator.take(2).toSeq
        if(seq.sizeIs > 1) {
          // If there is more than one matches, there is an ambiguity
          // Thus we don't return anything
          None
        } else {
          Some(seq.head)
        }
    }

    parametersOption.flatMap { case (leftIndices, rightIndices) =>
      unifyAllFormulas(conclusion.left.concat(conclusion.right), leftIndices.map(proofGoal.left).concat(rightIndices.map(proofGoal.right))) match {
        case UnificationSuccess(ctx) =>

          def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
            val set = indices.toSet
            for {
              (v, i) <- array.zipWithIndex
              if !set.contains(i)
            } yield v
          }

          val (commonLeft, commonRight) = (removeIndices(proofGoal.left, leftIndices), removeIndices(proofGoal.right, rightIndices))

          def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
            formulas.map { formula =>
              simultaneousNullaryFunctionSchemaInstantiation(
                simultaneousNullaryPredicateSchemaInstantiation(formula, ctx.predicates),
                ctx.functions
              )
            }

          val newGoals = application.rule.hypotheses.map(hypothesis =>
            ProofGoal(commonLeft ++ instantiate(hypothesis.left), commonRight ++ instantiate(hypothesis.right))
          )

          Some((newGoals, ctx))
        case UnificationFailure(message) => None
      }
    }
  }

  def mutateProofStateFirstGoal(proofState: ProofState, application: RuleApplication): Option[(ProofState, UnificationContext)] = {
    proofState.goals match {
      case h +: t =>
        mutateProofGoal(h, application).map { (newGoals, ctx) => (ProofState(newGoals ++ t), ctx) }
      case _ => None
    }
  }

  def proofGoalToSequent(proofGoal: ProofGoal): Sequent = Sequent(proofGoal.left.toSet, proofGoal.right.toSet)

  def reconstructSCProof(proofState: ProofState, applications: Seq[RuleApplication]): Option[SCProof] = {
    // Each proof goal that is created (or updated) will be given a unique id
    // Then we use these ids to refer to them as a proof step in the SC proof
    def recursive(nextId: Int, shadowProofState: IndexedSeq[Int], proofState: ProofState, remaining: Seq[RuleApplication]): Option[(SCProof, Map[Int, Int])] = remaining match {
      case appliedRule +: rest =>
        mutateProofStateFirstGoal(proofState, appliedRule) match {
          case Some((newState, ctx)) =>
            // The id of the goal that was transformed (here, it's always the first one)
            val id = shadowProofState.head
            val updatedGoal = proofState.goals.head
            // Number of goals that have been created (or updated), possibly zero
            // This corresponds to the number of premises in that rule
            val nReplacedGoals = appliedRule.rule.hypotheses.size // == newState.goals.size - proofState.goals.size + 1
            val newShadowGoals = nextId until (nextId + nReplacedGoals)
            // Updated shadow proof state (= ids for the new proof state)
            val newShadowProofState = newShadowGoals ++ shadowProofState.tail
            // We continue exploring the tree. The reconstruction happens when this function returns
            recursive(nextId + nReplacedGoals, newShadowProofState, newState, rest) match {
              case Some((proof, translation)) =>
                // Now we can reconstruct the SC proof steps
                val reconstructedSteps = appliedRule.rule.reconstruct(proofGoalToSequent(updatedGoal), ctx)
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
                Some((newProof, translation + (id -> (newProof.steps.size - 1))))
              case None => None
            }
          case None =>
            None
        }
      case _ => // Bottom of the front proof, now we go the other way
        // For a complete proof the proof state should be empty
        // However for testing purposes we may still allow incomplete proofs to exist,
        // and for that we should convert unclosed branches into imports
        val imports = proofState.goals.map(proofGoalToSequent)
        val initialTranslation = shadowProofState.zipWithIndex.map { case (v, i) => v -> -(i + 1) }.toMap
        Some((SCProof(IndexedSeq.empty, imports), initialTranslation))
    }
    // The final conclusion is given the id 0, although it will never be referenced as a premise
    recursive(proofState.goals.size, proofState.goals.indices, proofState, applications).map { case (proof, _) => proof }
  }


}
