package masterproject.front.proof

import lisa.kernel.proof.SCProof
import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.{Rewrite, SCProofStep}
import masterproject.SCUtils

trait ProofStateDefinitions extends SequentDefinitions with SequentOps {

  case class Proof(initialState: ProofState, steps: Seq[TacticApplication])

  final case class ProofState(goals: IndexedSeq[Sequent]) {
    override def toString: String =
      ((if (goals.nonEmpty) s"${goals.size} goal${if (goals.sizeIs > 1) "s" else ""}" else "[zero goals]") +:
        goals.map(_.toString)
        ).mkString("\n")
  }

  sealed abstract class Tactic

  abstract class GeneralTactic extends Tactic {
    // TODO uh, `TacticApplication`
    def apply(proofGoal: Sequent, app: TacticApplication): Option[(IndexedSeq[Sequent], ReconstructGeneral)]
  }

  type ReconstructGeneral = lisa.kernel.proof.SequentCalculus.Sequent => IndexedSeq[SCProofStep]

  type Reconstruct = (lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext) => IndexedSeq[SCProofStep]

  abstract class Rule extends Tactic {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    // The premises indexing is implicit:
    // * 0, 1, 2 will reference respectively the first, second and third steps in that array
    // * -1, -2, -3 will reference respectively the first second and third premises, as returned by `hypotheses`
    def reconstruct: Reconstruct

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(partials.forall(isSequentWellFormed))
    require(partials.flatMap(_.formulas).flatMap(f => predicatesOf(f) ++ functionsOf(f)).forall(_.arity == 0))
    require(partials.flatMap(schematicConnectorsOfSequent).forall(_.arity > 0)) // Please use predicates instead

    override def toString: String = {
      val top = hypotheses.map(_.toString).mkString(" " * 6)
      val bottom = conclusion.toString
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

  case object TacticApplyTheorem extends Tactic

  class RuleSolver(override val reconstruct: Reconstruct) extends Rule {
    override final def hypotheses: IndexedSeq[PartialSequent] = IndexedSeq.empty
    override final def conclusion: PartialSequent = PartialSequent(IndexedSeq.empty, IndexedSeq.empty)
  }

  class RuleIntroduction(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: Reconstruct) extends Rule
  class RuleElimination(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: Reconstruct) extends Rule
  // Possibly ambiguous (need additional context parameters)
  class RuleSubstitution(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: Reconstruct) extends Rule

  case class TacticApplication(
    tactic: Tactic,
    formulas: Option[(IndexedSeq[Int], IndexedSeq[Int])] = None,
    functions: Map[SchematicFunctionLabel[0], Term] = Map.empty,
    predicates: Map[SchematicPredicateLabel[0], Formula] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])] = Map.empty,
  )

  trait ReadableProofContext {
    def contains(sequent: Sequent): Boolean
  }

  def mutateProofGoal(proofGoal: Sequent, application: TacticApplication, proofContext: ReadableProofContext): Option[(IndexedSeq[Sequent], Option[Either[UnificationContext, ReconstructGeneral]])] = {
    application.tactic match {
      case TacticApplyTheorem =>
        if(proofContext.contains(proofGoal)) {
          Some((
            IndexedSeq.empty,
            None,
          ))
        } else {
          None
        }
      case general: GeneralTactic =>
        general(proofGoal, application).map { case (steps, f) => (steps, Some(Right(f))) }
      case rule: Rule =>
        val conclusion = rule.conclusion

        def parametersOption: Option[(IndexedSeq[Int], IndexedSeq[Int])] =
          if ((conclusion.partialLeft || conclusion.left.size == proofGoal.left.size) && (conclusion.partialRight || conclusion.right.size == proofGoal.right.size)) {
            application.formulas match {
              case Some(pair@(explicitLeft, explicitRight)) =>
                require(conclusion.left.size == explicitLeft.size)
                require(conclusion.right.size == explicitRight.size)
                Some(pair)
              case None =>
                def iterator = for {
                  leftIndices <- proofGoal.left.indices.combinations(conclusion.left.size).flatMap(_.permutations)
                  rightIndices <- proofGoal.right.indices.combinations(conclusion.right.size).flatMap(_.permutations)
                } yield (leftIndices, rightIndices)

                val seq = iterator.take(2).toSeq
                if (seq.sizeIs > 1) {
                  // If there is more than one matches, there is an ambiguity
                  // Thus we choose not to return anything
                  None
                } else {
                  Some(seq.head)
                }
            }
          } else {
            // Not matching exactly
            None
          }

        // We enumerate the schemas that appear at the top (of the rule) but not at the bottom
        // For these we have no other choice that to get a hint from the user
        val nonUnifiableFunctions = rule.hypotheses.flatMap(schematicFunctionsOfSequent).toSet
          .diff(schematicFunctionsOfSequent(rule.conclusion))
        val nonUnifiablePredicates = rule.hypotheses.flatMap(schematicPredicatesOfSequent).toSet
          .diff(schematicPredicatesOfSequent(rule.conclusion))

        // By assumption they must be of arity > 0
        // We require all connector schemas to be explicitly defined
        val connectorSchemas = (rule.hypotheses :+ rule.conclusion).flatMap(schematicConnectorsOfSequent).toSet

        // If the user enters invalid parameters, we choose to return None
        if (nonUnifiableFunctions == application.functions.keySet && nonUnifiablePredicates == application.predicates.keySet && connectorSchemas == application.connectors.keySet) {
          parametersOption.flatMap { case (leftIndices, rightIndices) =>
            val conclusionPatterns = conclusion.left.concat(conclusion.right)
            val conclusionTargets = leftIndices.map(proofGoal.left).concat(rightIndices.map(proofGoal.right))
            unifyAllFormulas(conclusionPatterns.map(instantiateConnectorSchemas(_, application.connectors)), conclusionTargets.map(instantiateConnectorSchemas(_, application.connectors))) match {
              case UnificationSuccess(ctx) =>
                // By assumption, they are disjoint
                // Not sure if that's the best idea to "update" the context, since this object is technically
                // owned by `Unification`
                val newCtx = UnificationContext(ctx.predicates ++ application.predicates, ctx.functions ++ application.functions, application.connectors)

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
                    instantiatePredicateSchemas(
                      instantiateFunctionSchemas(instantiateConnectorSchemas(formula, newCtx.connectors), newCtx.functions.view.mapValues(t => (t, Seq.empty[VariableLabel])).toMap),
                      newCtx.predicates.view.mapValues(p => (p, Seq.empty[VariableLabel])).toMap
                    )
                  }

                def createHypothesis(common: IndexedSeq[Formula], pattern: IndexedSeq[Formula], partial: Boolean): IndexedSeq[Formula] = {
                  val instantiated = instantiate(pattern)
                  if(partial) common ++ instantiated else instantiated
                }

                val newGoals = rule.hypotheses.map(hypothesis =>
                  Sequent(
                    createHypothesis(commonLeft, hypothesis.left, hypothesis.partialLeft),
                    createHypothesis(commonRight, hypothesis.right, hypothesis.partialRight),
                  )
                )

                Some((newGoals, Some(Left(newCtx))))
              case UnificationFailure(message) => None
            }
          }
        } else {
          None
        }
    }
  }

  def mutateProofStateFirstGoal(proofState: ProofState, application: TacticApplication, proofContext: ReadableProofContext): Option[(ProofState, Option[Either[UnificationContext, ReconstructGeneral]])] = {
    proofState.goals match {
      case h +: t =>
        mutateProofGoal(h, application, proofContext).map { (newGoals, ctx) => (ProofState(newGoals ++ t), ctx) }
      case _ => None
    }
  }

  def reconstructSCProof(proof: Proof, proofContext: ReadableProofContext): Option[(SCProof, Map[Int, Sequent])] = {
    // Each proof goal that is created (or updated) will be given a unique id
    // Then we use these ids to refer to them as a proof step in the SC proof
    def recursive(nextId: Int, shadowProofState: IndexedSeq[Int], proofState: ProofState, remaining: Seq[TacticApplication]): Option[(SCProof, Map[Int, Int], Map[Int, Sequent])] = remaining match {
      case appliedTactic +: rest =>
        mutateProofStateFirstGoal(proofState, appliedTactic, proofContext) match {
          case Some((newState, either)) =>
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
                val (reconstructedSteps, isTheorem) = (appliedTactic.tactic, either) match { // TODO fix this ugly wart
                  case (TacticApplyTheorem, None) =>
                    (IndexedSeq.empty, true)
                  case (rule: Rule, Some(Left(ctx))) =>
                    (rule.reconstruct(sequentToKernel(updatedGoal), ctx), false)
                  case (general: GeneralTactic, Some(Right(reconstructFunction))) =>
                    (reconstructFunction(sequentToKernel(updatedGoal)), false)
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
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
  }

}
