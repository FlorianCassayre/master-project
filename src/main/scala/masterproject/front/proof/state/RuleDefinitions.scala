package masterproject.front.proof.state

import lisa.kernel.proof.SequentCalculus.SCProofStep
import masterproject.front.unification.Unifier.*
import masterproject.front.fol.FOL.*

trait RuleDefinitions extends ProofStateDefinitions {

  type ReconstructRule = (lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext) => IndexedSeq[SCProofStep]

  abstract class Rule extends GeneralTactic {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(partials.forall(isSequentWellFormed))
    require(partials.flatMap(_.formulas).flatMap(f => predicatesOf(f) ++ functionsOf(f)).forall(_.arity == 0))
    require(partials.flatMap(schematicConnectorsOfSequent).forall(_.arity > 0)) // Please use predicates instead

    override def apply(proofGoal: Sequent, application: TacticParameters): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
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
      val nonUnifiableFunctions = hypotheses.flatMap(schematicFunctionsOfSequent).toSet
        .diff(schematicFunctionsOfSequent(conclusion))
      val nonUnifiablePredicates = hypotheses.flatMap(schematicPredicatesOfSequent).toSet
        .diff(schematicPredicatesOfSequent(conclusion))

      // By assumption they must be of arity > 0
      // We require all connector schemas to be explicitly defined
      val connectorSchemas = (hypotheses :+ conclusion).flatMap(schematicConnectorsOfSequent).toSet

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

              val newGoals = hypotheses.map(hypothesis =>
                Sequent(
                  createHypothesis(commonLeft, hypothesis.left, hypothesis.partialLeft),
                  createHypothesis(commonRight, hypothesis.right, hypothesis.partialRight),
                )
              )

              val reconstruction = () => reconstruct(proofGoal, newCtx)
              Some((newGoals, reconstruction))
            case UnificationFailure(message) => None
          }
        }
      } else {
        None
      }
    }

    override def toString: String = {
      val top = hypotheses.map(_.toString).mkString(" " * 6)
      val bottom = conclusion.toString
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

  class RuleIntroduction(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule
  class RuleElimination(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule
  // Possibly ambiguous (need additional context parameters)
  class RuleSubstitution(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

}
