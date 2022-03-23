package masterproject.front.proof.state

import lisa.kernel.proof.SequentCalculus.SCProofStep
import masterproject.front.unification.Unifier.*
import masterproject.front.fol.FOL.*

trait RuleDefinitions extends ProofStateDefinitions {

  type ReconstructRule = (lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext) => IndexedSeq[SCProofStep]

  case class RuleTacticParameters(
    formulas: Option[(IndexedSeq[Int], IndexedSeq[Int])] = None,
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])] = Map.empty,
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])] = Map.empty,
  ) {
    def withIndices(left: Int*)(right: Int*): RuleTacticParameters =
      copy(formulas = Some((left.toIndexedSeq, right.toIndexedSeq)))
    def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], value: Term, parameters: FillTuple[VariableLabel, N]
    ): RuleTacticParameters =
      copy(functions = functions + (label -> (value, parameters.toSeq)))
    def withFunction(label: SchematicFunctionLabel[0], value: Term): RuleTacticParameters =
      withFunction(label, value, EmptyTuple)
    def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], value: Formula, parameters: FillTuple[VariableLabel, N]
    ): RuleTacticParameters =
      copy(predicates = predicates + (label -> (value, parameters.toSeq)))
    def withPredicate(label: SchematicPredicateLabel[0], value: Formula): RuleTacticParameters =
      withPredicate(label, value, EmptyTuple)
    def withConnector[N <: Arity](
      label: SchematicConnectorLabel[N], value: Formula, parameters: FillTuple[SchematicPredicateLabel[0], N]
    ): RuleTacticParameters = {
      require(label.arity > 0, "For consistency, use nullary predicate schemas instead of connectors")
      copy(connectors = connectors + (label -> (value, parameters.toSeq)))
    }
  }
  val RuleTacticParametersBuilder: RuleTacticParameters = RuleTacticParameters()

  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleTacticParameters) extends GeneralTactic {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      val conclusion = rule.conclusion
      val hypotheses = rule.hypotheses
      val reconstruct = rule.reconstruct
      def parametersOption: Option[(IndexedSeq[Int], IndexedSeq[Int])] =
        if ((conclusion.partialLeft || conclusion.left.size == proofGoal.left.size) && (conclusion.partialRight || conclusion.right.size == proofGoal.right.size)) {
          parameters.formulas match {
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

      val allFormulas = hypotheses :+ conclusion

      // We enumerate the schemas that appear at the top (of the rule) but not at the bottom
      // For these we have no other choice that to get a hint from the user
      val nonUnifiableFunctions = hypotheses.flatMap(schematicFunctionsOfSequent).toSet
        .diff(schematicFunctionsOfSequent(conclusion))
      val nonUnifiablePredicates = hypotheses.flatMap(schematicPredicatesOfSequent).toSet
        .diff(schematicPredicatesOfSequent(conclusion))

      // We enumerate the schemas of arity > 0
      val ruleFunctions = allFormulas.flatMap(schematicFunctionsOfSequent).toSet
      val rulePredicates = allFormulas.flatMap(schematicPredicatesOfSequent).toSet
      // By assumption connectors must be of arity > 0
      val ruleConnectors = allFormulas.flatMap(schematicConnectorsOfSequent).toSet
      assert(ruleConnectors.forall(_.arity > 0))

      val parametersFunctions = parameters.functions.keySet
      val parametersPredicates = parameters.predicates.keySet
      val parametersConnectors = parameters.connectors.keySet

      // 0. Assignments should be well-formed TODO: call isWellFormed
      lazy val noMalformedAssignment =
        parameters.functions.forall { case (label, (_, args)) => label.arity == args.size } &&
          parameters.predicates.forall { case (label, (_, args)) => label.arity == args.size } &&
          parameters.connectors.forall { case (label, (_, args)) => label.arity == args.size }
      // 1. All the parameters must be declared symbols
      lazy val noUnknownSymbols =
        parametersFunctions.subsetOf(ruleFunctions) &&
          parametersPredicates.subsetOf(rulePredicates) &&
          parametersConnectors.subsetOf(ruleConnectors)
      // 2. All symbols defined as non-unifiable must appear in the parameters
      lazy val noUndeclaredNonUnifiable =
        nonUnifiableFunctions.subsetOf(parametersFunctions) &&
          nonUnifiablePredicates.subsetOf(parametersPredicates)
      // 3. All schemas of arity > 0 must be declared explicitly
      lazy val noUndeclaredHigherOrder =
        ruleFunctions.filter(_.arity > 0).subsetOf(parametersFunctions) &&
          rulePredicates.filter(_.arity > 0).subsetOf(parametersPredicates) &&
          ruleConnectors.subsetOf(parametersConnectors)

      // This function ensures that the parameters do not contradict a resolution
      def contextMatchesParameters(ctx: UnificationContext): Boolean = {
        ctx.functions.filter(_._1.arity == 0).forall { case (label, (t1, _)) =>
          parameters.functions.get(label).forall { case (t2, _) => isSame(t1, t2) }
        } &&
          ctx.predicates.filter(_._1.arity == 0).forall { case (label, (t1, _)) =>
            parameters.predicates.get(label).forall { case (t2, _) => isSame(t1, t2) }
          }
      }

      // If the user enters invalid parameters, we return None
      if (noMalformedAssignment && noUnknownSymbols && noUndeclaredNonUnifiable && noUndeclaredHigherOrder) {
        parametersOption.filter { case (leftIndices, rightIndices) =>
          leftIndices.forall(proofGoal.left.indices.contains) && rightIndices.forall(proofGoal.right.indices.contains)
        }.flatMap { case (leftIndices, rightIndices) =>
          val conclusionPatterns = conclusion.left.concat(conclusion.right)
          val conclusionTargets = leftIndices.map(proofGoal.left).concat(rightIndices.map(proofGoal.right))
          unifyAllFormulas(conclusionPatterns, conclusionTargets) match {
            case UnificationSuccess(ctx) if contextMatchesParameters(ctx) =>

              val newCtx = UnificationContext(
                ctx.predicates ++ parameters.predicates,
                ctx.functions ++ parameters.functions,
                ctx.connectors ++ parameters.connectors,
                ctx.variables,
              )

              def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
                val set = indices.toSet
                for {
                  (v, i) <- array.zipWithIndex
                    if !set.contains(i)
                } yield v
              }

              val (commonLeft, commonRight) = (removeIndices(proofGoal.left, leftIndices), removeIndices(proofGoal.right, rightIndices))

              def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
                formulas.map(formula => instantiateSchemas(formula, newCtx.functions, newCtx.predicates, newCtx.connectors))

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
            case _ => None // Contradiction or unification failure
          }
        }
      } else {
        None
      }
    }

    override def toString: String = {
      val top = rule.hypotheses.map(_.toString).mkString(" " * 6)
      val bottom = rule.conclusion.toString
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

  abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(partials.forall(isSequentWellFormed))
    require(partials.flatMap(schematicConnectorsOfSequent).forall(_.arity > 0)) // Please use predicates instead

    final def apply(parameters: RuleTacticParameters = RuleTacticParameters()): RuleTactic =
      RuleTactic(this, parameters)
  }

  class RuleIntroduction(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule
  class RuleElimination(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule
  // Possibly ambiguous (need additional context parameters)
  class RuleSubstitution(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

}
