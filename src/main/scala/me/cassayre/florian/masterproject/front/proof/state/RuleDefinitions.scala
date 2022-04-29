package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.proof.SequentCalculus.{SCProofStep, SCSubproof}
import me.cassayre.florian.masterproject.front.unification.Unifier
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.unification.UnificationUtils

import scala.collection.View

trait RuleDefinitions extends ProofEnvironmentDefinitions with UnificationUtils {

  type ReconstructRule = PartialFunction[(lisa.kernel.proof.SequentCalculus.Sequent, Unifier.UnificationContext), IndexedSeq[SCProofStep]]
  type SequentSelector = (IndexedSeq[Int], IndexedSeq[Int])

  case class RuleParameters(
    selectors: Map[Int, SequentSelector] = Map.empty,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  ) {
    def withIndices(i: Int)(left: Int*)(right: Int*): RuleParameters = {
      val pair = (left.toIndexedSeq, right.toIndexedSeq)
      copy(selectors = selectors + (i -> pair))
    }

    def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], f: FillArgs[SchematicFunctionLabel[0], N] => Term
    )(using ValueOf[N]): RuleParameters =
      copy(functions = functions :+ AssignedFunction(label, LambdaFunction[N](f)))
    def withFunction(label: SchematicFunctionLabel[0], value: Term): RuleParameters =
      withFunction(label, _ => value)

    def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], f: FillArgs[SchematicFunctionLabel[0], N] => Formula
    )(using ValueOf[N]): RuleParameters = copy(predicates = predicates :+ AssignedPredicate(label, LambdaPredicate(f)))
    def withPredicate(label: SchematicPredicateLabel[0], value: Formula): RuleParameters =
      withPredicate(label, _ => value)

    def withConnector[N <: Arity](
      label: SchematicConnectorLabel[N], f: FillArgs[SchematicPredicateLabel[0], N] => Formula
    )(using ValueOf[N]): RuleParameters = {
      require(label.arity > 0, "For consistency, use nullary predicate schemas instead of connectors")
      copy(connectors = connectors :+ AssignedConnector(label, LambdaConnector(f)))
    }

    def withVariables(label: VariableLabel, value: VariableLabel): RuleParameters =
      copy(variables = variables + (label -> value))
  }

  protected def matchIndices(map: Map[Int, SequentSelector], patterns: IndexedSeq[PartialSequent], values: IndexedSeq[Sequent]): View[IndexedSeq[SequentSelector]] = {
    require(patterns.size == values.size)
    // Normally `pattern` shouldn't be empty, but this function works regardless
    if(map.keySet.forall(patterns.indices.contains)) {
      val selectors = patterns.indices.map(map.getOrElse(_, (IndexedSeq.empty, IndexedSeq.empty)))
      selectors.zip(patterns.zip(values)).map { case ((leftSelector, rightSelector), (pattern, value)) =>
        def enumerate(selectorSide: IndexedSeq[Int], patternSideSize: Int, isPatternPartial: Boolean, valueSide: Range): View[IndexedSeq[Int]] = {
          // TODO remove the partial parameter as it is not needed in this direction
          if(selectorSide.isEmpty) { // If empty we consider all permutations
            // If `valueSide` is empty then it will produce an empty array
            valueSide.combinations(patternSideSize).flatMap(_.permutations).toSeq.view
          } else {
            if(selectorSide.size == patternSideSize) {
              if(selectorSide.forall(valueSide.contains)) {
                // We return exactly what was selected
                View(selectorSide)
              } else {
                // An index value is out of range
                View.empty
              }
            } else {
              // Number of args does not match the pattern's
              View.empty
            }
          }
        }
        val leftSide = enumerate(leftSelector, pattern.left.size, pattern.partialLeft, value.left.indices)
        val rightSide = enumerate(rightSelector, pattern.right.size, pattern.partialRight, value.right.indices)
        for {
          l <- leftSide
            r <- rightSide
        } yield IndexedSeq((l, r))
      }.fold(View(IndexedSeq.empty[(IndexedSeq[Int], IndexedSeq[Int])])) { case (v1, v2) =>
        for {
          first <- v1
            second <- v2
        } yield first ++ second
      }
    } else {
      // Map contains values outside the range
      View.empty
    }
  }

  protected def inflateValues(patternsTo: IndexedSeq[PartialSequent], valuesFrom: IndexedSeq[Sequent], ctx: Unifier.UnificationContext, indices: IndexedSeq[(IndexedSeq[Int], IndexedSeq[Int])]): IndexedSeq[Sequent] = {
    def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
      val set = indices.toSet
      for {
        (v, i) <- array.zipWithIndex
          if !set.contains(i)
      } yield v
    }

    def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
      formulas.map(formula => instantiateFormulaSchemas(formula, functions = ctx.assignedFunctions, predicates = ctx.assignedPredicates, connectors = ctx.assignedConnectors))

    def createValueTo(common: IndexedSeq[Formula], pattern: IndexedSeq[Formula], partial: Boolean): IndexedSeq[Formula] = {
      val instantiated = instantiate(pattern)
      if(partial) common ++ instantiated else instantiated
    }

    val (commonLeft, commonRight) = {
      indices.zip(valuesFrom).map { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) => // Union all
        (removeIndices(valueLeft, indicesLeft), removeIndices(valueRight, indicesRight))
      }.foldLeft((IndexedSeq.empty[Formula], IndexedSeq.empty[Formula])) { case ((accL, accR), ((ls, rs))) =>
        (accL ++ ls.diff(accL), accR ++ rs.diff(accR))
      }
    }

    val newValues = patternsTo.map(patternTo =>
      Sequent(
        createValueTo(commonLeft, patternTo.left, patternTo.partialLeft),
        createValueTo(commonRight, patternTo.right, patternTo.partialRight),
      )
    )

    newValues
  }

  protected def applyRuleInference(
    parameters: RuleParameters,
    patternsFrom: IndexedSeq[PartialSequent],
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
    extraFunctions: Set[SchematicFunctionLabel[?]],
    extraPredicate: Set[SchematicPredicateLabel[?]],
    extraConnectors: Set[SchematicConnectorLabel[?]],
    //extraVariables: Set[VariableLabel] = Set.empty,
  ): Option[(IndexedSeq[Sequent], Unifier.UnificationContext)] = {
    def parametersOption: View[IndexedSeq[SequentSelector]] =
      if(patternsFrom.size == valuesFrom.size) {
        matchIndices(parameters.selectors, patternsFrom, valuesFrom)
      } else {
        View.empty
      }

    val allPartialFormulas = patternsFrom ++ patternsTo

    // We enumerate the schemas that appear at the top (of the rule) but not at the bottom
    // For these we have no other choice that to get a hint from the user
    val nonUnifiableFunctions = patternsTo.flatMap(schematicFunctionsOfSequent).toSet
      .diff(patternsFrom.flatMap(schematicFunctionsOfSequent).toSet)
    val nonUnifiablePredicates = patternsTo.flatMap(schematicPredicatesOfSequent).toSet
      .diff(patternsFrom.flatMap(schematicPredicatesOfSequent).toSet)

    // We enumerate the schemas of arity > 0
    val ruleFunctions = allPartialFormulas.flatMap(schematicFunctionsOfSequent).toSet ++ extraFunctions
    val rulePredicates = allPartialFormulas.flatMap(schematicPredicatesOfSequent).toSet ++ extraPredicate
    // By assumption connectors must be of arity > 0
    val ruleConnectors = allPartialFormulas.flatMap(schematicConnectorsOfSequent).toSet ++ extraConnectors
    assert(ruleConnectors.forall(_.arity > 0))

    val parametersFunctions = parameters.functions.map(_.schema).toSet
    val parametersPredicates = parameters.predicates.map(_.schema).toSet
    val parametersConnectors = parameters.connectors.map(_.schema).toSet

    lazy val isExactlyParametrized =
      ruleFunctions == parametersFunctions &&
        rulePredicates == parametersPredicates &&
        ruleConnectors == parametersConnectors

    // 0. Assignments should be well-formed (arity matches, arguments are distinct, body is well formed, no free variables or schematic connectors)
    lazy val noMalformedAssignment =
      parameters.functions.forall { case AssignedFunction(label, LambdaFunction(args, t)) =>
        isWellFormed(t) && freeVariablesOf(t).isEmpty
      } &&
        parameters.predicates.forall { case AssignedPredicate(label, LambdaPredicate(args, f)) =>
          isWellFormed(f) && freeVariablesOf(f).isEmpty && schematicConnectorsOf(f).isEmpty
        } &&
        parameters.connectors.forall { case AssignedConnector(label, LambdaConnector(args, f)) =>
          isWellFormed(f) && freeVariablesOf(f).isEmpty && schematicConnectorsOf(f).isEmpty
        }
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

    // If the user enters invalid parameters, we return None
    if (noMalformedAssignment && noUnknownSymbols && noUndeclaredNonUnifiable && noUndeclaredHigherOrder) {
      // Schemas appearing in parametrized bodies
      // We should consider them as values
      // What we do is to temporarily rename pattern schemas so that they don't collide
      // Then we force-assign the value schemas themselves, and at the end we rename the keys of the mapping
      val functionsInBodies = (
        parameters.functions.flatMap(a => schematicFunctionsOf(a.lambda.body)) ++
          parameters.predicates.flatMap(a => schematicFunctionsOf(a.lambda.body)) ++
          parameters.connectors.flatMap(a => schematicFunctionsOf(a.lambda.body))).toSet
      val predicatesInBodies = (
        parameters.predicates.flatMap(a => schematicPredicatesOf(a.lambda.body)) ++
          parameters.connectors.flatMap(a => schematicPredicatesOf(a.lambda.body))).toSet
      val patternFunctionsToRename = ruleFunctions.intersect(functionsInBodies)
      val patternPredicatesToRename = rulePredicates.intersect(predicatesInBodies)
      val (_, functionsMapping) = patternFunctionsToRename.foldLeft(((ruleFunctions ++ functionsInBodies).map(_.id), Seq.empty[RenamedFunctionSchema])) {
        case ((taken, map), f) =>
          val newId = freshId(taken, f.id)
          val newSchema = SchematicFunctionLabel.unsafe(newId, f.arity)
          (taken + newId, map :+ RenamedLabel.unsafe(f, newSchema))
      }
      val functionsMappingMap: Map[SchematicFunctionLabel[?], SchematicFunctionLabel[?]] = functionsMapping.map(r => r.from -> r.to).toMap
      val (_, predicatesMapping) = patternPredicatesToRename.foldLeft(((rulePredicates ++ predicatesInBodies).map(_.id), Seq.empty[RenamedPredicateSchema])) {
        case ((taken, map), f) =>
          val newId = freshId(taken, f.id)
          val newSchema = SchematicPredicateLabel.unsafe(newId, f.arity)
          (taken + newId, map :+ RenamedLabel.unsafe(f, newSchema))
      }
      val predicatesMappingMap: Map[SchematicPredicateLabel[?], SchematicPredicateLabel[?]] = predicatesMapping.map(r => r.from -> r.to).toMap
      def instantiatePatternsMappings(patterns: IndexedSeq[PartialSequent]): IndexedSeq[PartialSequent] =
        patterns.map(partial =>
          partial.copy(
            left = partial.left.map(instantiateFormulaSchemas(_, functions = functionsMapping.map(_.toAssignment), predicates = predicatesMapping.map(_.toAssignment))),
            right = partial.right.map(instantiateFormulaSchemas(_, functions = functionsMapping.map(_.toAssignment), predicates = predicatesMapping.map(_.toAssignment))),
          )
        )
          .map { partial =>
            def instantiate(seq: IndexedSeq[Formula]): IndexedSeq[Formula] =
              seq.map(instantiateFormulaSchemas(_, functions = parameters.functions, predicates = parameters.predicates, connectors = parameters.connectors))
            partial.copy(left = instantiate(partial.left), right = instantiate(partial.right))
          }
      val patternFromRenamedInstantiated = instantiatePatternsMappings(patternsFrom)
      val patternToRenamedInstantiated = instantiatePatternsMappings(patternsTo)

      val (reverseFunctionsMapping, reversePredicatesMapping) = (functionsMapping.map(_.swap), predicatesMapping.map(_.swap))
      val (reverseFunctionsMappingMap, reversePredicatesMappingMap) =
        (reverseFunctionsMapping.map(r => r.from -> r.to).toMap.asInstanceOf[Map[SchematicFunctionLabel[?], SchematicFunctionLabel[?]]], reversePredicatesMapping.map(r => r.from -> r.to).toMap.asInstanceOf[Map[SchematicPredicateLabel[?], SchematicPredicateLabel[?]]])

      val formulaPatternsFrom = patternFromRenamedInstantiated.flatMap(p => p.left ++ p.right)

      parametersOption.flatMap { indices =>
        val formulaValueFrom = indices.zip(valuesFrom).flatMap { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) =>
          indicesLeft.map(valueLeft) ++ indicesRight.map(valueRight)
        }
        val initialContext = Unifier.UnificationContext(
          parameters.predicates.map(a => predicatesMappingMap.getOrElse(a.schema, a.schema) -> a.lambda).toMap,
          parameters.functions.map(a => functionsMappingMap.getOrElse(a.schema, a.schema) -> a.lambda).toMap,
          parameters.connectors.map(a => a.schema -> a.lambda).toMap,
          Map.empty,
        )
        Unifier.unifyAllFormulas(formulaPatternsFrom, formulaValueFrom, initialContext) match {
          case Unifier.UnificationSuccess(ctxRenamed) =>

            // We safely restore the original schema names, recursively
            val newCtx = Unifier.UnificationContext(
              ctxRenamed.predicates.map { case (k, v) => reversePredicatesMappingMap.getOrElse(k, k) -> v },
              ctxRenamed.functions.map { case (k, v) => reverseFunctionsMappingMap.getOrElse(k, k) -> v },
              ctxRenamed.connectors,
              ctxRenamed.variables,
            )

            val newValues = inflateValues(patternToRenamedInstantiated, valuesFrom, ctxRenamed, indices)

            Some((newValues, newCtx))
          case _ => None // Contradiction or unification failure
        }
      }.headOption
    } else {
      None
    }
  }

  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleParameters) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      applyRuleInference(parameters, IndexedSeq(rule.conclusion), rule.hypotheses, IndexedSeq(proofGoal), Set.empty, Set.empty, Set.empty).flatMap {
        case (newGoals, ctx) =>
          val stepsOption = rule.reconstruct.andThen(Some.apply).applyOrElse((proofGoal, ctx), _ => None)
          stepsOption.map(steps => (newGoals, () => steps))
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

  sealed abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(isLegalPatterns(hypotheses) && isLegalPatterns(IndexedSeq(conclusion)))

    final def apply(parameters: RuleParameters = RuleParameters()): RuleTactic =
      RuleTactic(this, parameters)

    final def apply(justification0: Justified, rest: Justified*): Option[Theorem] =
      apply(RuleParameters())((justification0 +: rest): _*)(using justification0.environment)
    /*final def apply(parameters: RuleParameters)(justification0: Justified, rest: Justified*): Option[Theorem] = {
      val env = justification0.environment
      val justifications = justification0 +: rest
      apply(parameters)(justifications: _*)(using env)
    }*/
    final def apply(parameters: RuleParameters)(using env: ProofEnvironment): Option[Theorem] =
      apply(parameters)()

    final def apply(parameters: RuleParameters)(justifications: Justified*)(using env: ProofEnvironment): Option[Theorem] = {
      val justificationsSeq = justifications.toIndexedSeq
      val topSequents = justificationsSeq.map(_.sequent)
      applyRuleInference(parameters, hypotheses, IndexedSeq(conclusion), topSequents, Set.empty, Set.empty, Set.empty).flatMap {
        case (IndexedSeq(newSequent), ctx) =>
          reconstruct.andThen(Some.apply).applyOrElse((newSequent, ctx), _ => None).map { scSteps =>
            val scProof = lisa.kernel.proof.SCProof(scSteps, justificationsSeq.map(_.sequentAsKernel))
            env.mkTheorem(newSequent, scProof, justificationsSeq)
          }
        case _ => throw new Error
      }
    }
  }

  class RuleBase(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

  given Conversion[Rule, RuleTactic] = _()

}
