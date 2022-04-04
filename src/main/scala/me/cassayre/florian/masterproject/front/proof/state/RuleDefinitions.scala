package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.proof.SequentCalculus.{SCProofStep, SCSubproof}
import me.cassayre.florian.masterproject.front.unification.Unifier.*
import me.cassayre.florian.masterproject.front.fol.FOL.*

import scala.collection.View

trait RuleDefinitions extends ProofEnvironmentDefinitions {

  type ReconstructRule = PartialFunction[(lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext), IndexedSeq[SCProofStep]]

  sealed abstract class CommonRuleParameters {
    protected type T <: CommonRuleParameters

    val selectors: Map[Int, SequentSelector]
    val functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]
    val predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])]
    val connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])]

    def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], value: Term, parameters: FillArgs[VariableLabel, N]
    ): T
    final def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], f: FillArgs[VariableLabel, N] => Term
    ): T = {
      val (parameters, value) = fillTupleParametersFunction(label.arity, f)
      withFunction(label, value, parameters)
    }
    final def withFunction(label: SchematicFunctionLabel[0], value: Term): T =
      withFunction(label, value, EmptyTuple)
    def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], value: Formula, parameters: FillArgs[VariableLabel, N]
    ): T
    final def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], f: FillArgs[VariableLabel, N] => Formula
    ): T = {
      val (parameters, value) = fillTupleParametersPredicate(label.arity, f)
      withPredicate(label, value, parameters)
    }
    final def withPredicate(label: SchematicPredicateLabel[0], value: Formula): T =
      withPredicate(label, value, EmptyTuple)
    protected def withConnectorInternal[N <: Arity](
      label: SchematicConnectorLabel[N], value: Formula, parameters: FillArgs[SchematicPredicateLabel[0], N]
    ): T
    final def withConnector[N <: Arity](
      label: SchematicConnectorLabel[N], value: Formula, parameters: FillArgs[SchematicPredicateLabel[0], N]
    ): T = {
      require(label.arity > 0, "For consistency, use nullary predicate schemas instead of connectors")
      withConnectorInternal(label, value, parameters)
    }
    final def withConnector[N <: Arity](
      label: SchematicConnectorLabel[N], f: FillArgs[SchematicPredicateLabel[0], N] => Formula
    ): T = {
      val (parameters, value) = fillTupleParametersConnector(label.arity, f)
      withConnector(label, value, parameters)
    }
  }

  type SequentSelector = (IndexedSeq[Int], IndexedSeq[Int])

  case class RuleBackwardParameters(
    selector: SequentSelector = (IndexedSeq.empty, IndexedSeq.empty),
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])] = Map.empty,
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])] = Map.empty,
  ) extends CommonRuleParameters {
    override type T = RuleBackwardParameters

    override val selectors: Map[Int, SequentSelector] = Map(0 -> selector)

    def withIndices(left: Int*)(right: Int*): RuleBackwardParameters =
      copy(selector = (left.toIndexedSeq, right.toIndexedSeq))
    override def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], value: Term, parameters: FillArgs[VariableLabel, N]
    ): RuleBackwardParameters =
      copy(functions = functions + (label -> (value, parameters.toSeq)))
    override def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], value: Formula, parameters: FillArgs[VariableLabel, N]
    ): RuleBackwardParameters =
      copy(predicates = predicates + (label -> (value, parameters.toSeq)))
    override protected def withConnectorInternal[N <: Arity](
      label: SchematicConnectorLabel[N], value: Formula, parameters: FillArgs[SchematicPredicateLabel[0], N]
    ): RuleBackwardParameters =
      copy(connectors = connectors + (label -> (value, parameters.toSeq)))
  }
  val RuleBackwardParametersBuilder: RuleBackwardParameters = RuleBackwardParameters()

  case class RuleForwardParameters(
    selectors: Map[Int, SequentSelector] = Map.empty,
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])] = Map.empty,
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])] = Map.empty,
  ) extends CommonRuleParameters {
    override type T = RuleForwardParameters

    def withIndices(i: Int)(left: Int*)(right: Int*): RuleForwardParameters = {
      val pair = (left.toIndexedSeq, right.toIndexedSeq)
      copy(selectors = selectors + (i -> pair))
    }
    override def withFunction[N <: Arity](
      label: SchematicFunctionLabel[N], value: Term, parameters: FillArgs[VariableLabel, N]
    ): RuleForwardParameters =
      copy(functions = functions + (label -> (value, parameters.toSeq)))
    override def withPredicate[N <: Arity](
      label: SchematicPredicateLabel[N], value: Formula, parameters: FillArgs[VariableLabel, N]
    ): RuleForwardParameters =
      copy(predicates = predicates + (label -> (value, parameters.toSeq)))
    override protected def withConnectorInternal[N <: Arity](
      label: SchematicConnectorLabel[N], value: Formula, parameters: FillArgs[SchematicPredicateLabel[0], N]
    ): RuleForwardParameters =
      copy(connectors = connectors + (label -> (value, parameters.toSeq)))
  }
  val RuleForwardParametersBuilder: RuleForwardParameters = RuleForwardParameters()

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

  protected def applyRuleInference(
    parameters: CommonRuleParameters,
    patternsFrom: IndexedSeq[PartialSequent],
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {
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
    val ruleFunctions = allPartialFormulas.flatMap(schematicFunctionsOfSequent).toSet
    val rulePredicates = allPartialFormulas.flatMap(schematicPredicatesOfSequent).toSet
    // By assumption connectors must be of arity > 0
    val ruleConnectors = allPartialFormulas.flatMap(schematicConnectorsOfSequent).toSet
    assert(ruleConnectors.forall(_.arity > 0))

    val parametersFunctions = parameters.functions.keySet
    val parametersPredicates = parameters.predicates.keySet
    val parametersConnectors = parameters.connectors.keySet

    lazy val isExactlyParametrized =
      ruleFunctions == parametersFunctions &&
        rulePredicates == parametersPredicates &&
        ruleConnectors == parametersConnectors

    // 0. Assignments should be well-formed (arity matches, arguments are distinct, body is well formed, no free variables or schematic connectors)
    lazy val noMalformedAssignment =
    parameters.functions.forall { case (label, (t, args)) =>
      label.arity == args.size && args.distinct == args && isWellFormed(t) && freeVariablesOf(t).subsetOf(args.toSet)
    } &&
      parameters.predicates.forall { case (label, (f, args)) =>
        label.arity == args.size && args.distinct == args && isWellFormed(f) && freeVariablesOf(f).subsetOf(args.toSet) && schematicConnectorsOf(f).isEmpty
      } &&
      parameters.connectors.forall { case (label, (f, args)) =>
        label.arity == args.size && args.distinct == args && isWellFormed(f) && freeVariablesOf(f).isEmpty && schematicConnectorsOf(f).isEmpty
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
        parameters.functions.values.flatMap { case (t, _) => schematicFunctionsOf(t) } ++
          parameters.predicates.values.flatMap { case (f, _) => schematicFunctionsOf(f) } ++
          parameters.connectors.values.flatMap { case (f, _) => schematicFunctionsOf(f) }).toSet
      val predicatesInBodies = (
        parameters.predicates.values.flatMap { case (f, _) => schematicPredicatesOf(f) } ++
          parameters.connectors.values.flatMap { case (f, _) => schematicPredicatesOf(f) }).toSet
      val patternFunctionsToRename = ruleFunctions.intersect(functionsInBodies)
      val patternPredicatesToRename = rulePredicates.intersect(predicatesInBodies)
      val (_, functionsMapping) = patternFunctionsToRename.foldLeft(((ruleFunctions ++ functionsInBodies).map(_.id), Map.empty[SchematicFunctionLabel[?], SchematicFunctionLabel[?]])) {
        case ((taken, map), f) =>
          val newId = freshId(taken, f.id)
          val newSchema = SchematicFunctionLabel.unsafe(newId, f.arity)
          (taken + newId, map + (f -> newSchema))
      }
      val (_, predicatesMapping) = patternPredicatesToRename.foldLeft(((rulePredicates ++ predicatesInBodies).map(_.id), Map.empty[SchematicPredicateLabel[?], SchematicPredicateLabel[?]])) {
        case ((taken, map), f) =>
          val newId = freshId(taken, f.id)
          val newSchema = SchematicPredicateLabel.unsafe(newId, f.arity)
          (taken + newId, map + (f -> newSchema))
      }
      def instantiatePatternsMappings(patterns: IndexedSeq[PartialSequent]): IndexedSeq[PartialSequent] =
        patterns.map(partial =>
          partial.copy(
            left = partial.left.map(renameSchemas(_, functionsMapping, predicatesMapping, Map.empty, Map.empty)),
            right = partial.right.map(renameSchemas(_, functionsMapping, predicatesMapping, Map.empty, Map.empty)),
          )
        )
        .map { partial =>
          def instantiate(seq: IndexedSeq[Formula]): IndexedSeq[Formula] =
            seq.map(instantiateSchemas(_, parameters.functions, parameters.predicates, parameters.connectors))
          partial.copy(left = instantiate(partial.left), right = instantiate(partial.right))
        }
      val patternFromRenamedInstantiated = instantiatePatternsMappings(patternsFrom)
      val patternToRenamedInstantiated = instantiatePatternsMappings(patternsTo)

      val (reverseFunctionsMapping, reversePredicatesMapping) = (functionsMapping.map(_.swap), predicatesMapping.map(_.swap))

      val formulaPatternsFrom = patternFromRenamedInstantiated.flatMap(p => p.left ++ p.right)

      parametersOption.flatMap { indices =>
        val formulaValueFrom = indices.zip(valuesFrom).flatMap { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) =>
          indicesLeft.map(valueLeft) ++ indicesRight.map(valueRight)
        }
        val initialContext = UnificationContext(
          parameters.predicates.map { case (k, v) => predicatesMapping.getOrElse(k, k) -> v },
          parameters.functions.map { case (k, v) => functionsMapping.getOrElse(k, k) -> v },
          parameters.connectors,
          Map.empty,
        )
        unifyAllFormulas(formulaPatternsFrom, formulaValueFrom, initialContext) match {
          case UnificationSuccess(ctxRenamed) =>

            // We safely restore the original schema names, recursively
            val newCtx = UnificationContext(
              ctxRenamed.predicates.map { case (k, v) => reversePredicatesMapping.getOrElse(k, k) -> v },
              ctxRenamed.functions.map { case (k, v) => reverseFunctionsMapping.getOrElse(k, k) -> v },
              ctxRenamed.connectors,
              ctxRenamed.variables,
            )

            def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
              val set = indices.toSet
              for {
                (v, i) <- array.zipWithIndex
                  if !set.contains(i)
              } yield v
            }

            def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
              formulas.map(formula => instantiateSchemas(formula, ctxRenamed.functions, ctxRenamed.predicates, ctxRenamed.connectors))

            def createValueTo(common: IndexedSeq[Formula], pattern: IndexedSeq[Formula], partial: Boolean): IndexedSeq[Formula] = {
              val instantiated = instantiate(pattern)
              if(partial) common ++ instantiated else instantiated
            }

            val (commonLeft, commonRight) = indices.zip(valuesFrom).map { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) => // Union all
              (removeIndices(valueLeft, indicesLeft), removeIndices(valueRight, indicesRight))
            }.reduce { case ((l1, r1), (l2, r2)) =>
              (l1 ++ l2.diff(l1), r1 ++ r2.diff(r1))
            }

            val newValues = patternToRenamedInstantiated.map(patternTo =>
              Sequent(
                createValueTo(commonLeft, patternTo.left, patternTo.partialLeft),
                createValueTo(commonRight, patternTo.right, patternTo.partialRight),
              )
            )

            Some((newValues, newCtx))
          case _ => None // Contradiction or unification failure
        }
      }.headOption
    } else {
      None
    }
  }

  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleBackwardParameters) extends GeneralTactic {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      applyRuleInference(parameters, IndexedSeq(rule.conclusion), rule.hypotheses, IndexedSeq(proofGoal)).flatMap {
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

  abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(partials.forall(isSequentWellFormed))
    require(partials.flatMap(schematicConnectorsOfSequent).forall(_.arity > 0)) // Please use predicates instead

    final def apply(parameters: RuleBackwardParameters = RuleBackwardParametersBuilder): RuleTactic =
      RuleTactic(this, parameters)

    final def apply(justification0: Justified, rest: Justified*): Option[Theorem] =
      apply(RuleForwardParametersBuilder)((justification0 +: rest): _*)(using justification0.environment)
    /*final def apply(parameters: RuleForwardParameters)(justification0: Justified, rest: Justified*): Option[Theorem] = {
      val env = justification0.environment
      val justifications = justification0 +: rest
      apply(parameters)(justifications: _*)(using env)
    }*/
    final def apply(parameters: RuleForwardParameters)(using env: ProofEnvironment): Option[Theorem] =
      apply(parameters)()

    final def apply(parameters: RuleForwardParameters)(justifications: Justified*)(using env: ProofEnvironment): Option[Theorem] = {
      val justificationsSeq = justifications.toIndexedSeq
      applyRuleInference(parameters, hypotheses, IndexedSeq(conclusion), justificationsSeq.map(_.sequent)).flatMap {
        case (IndexedSeq(newSequent), ctx) =>
          reconstruct.andThen(Some.apply).applyOrElse((newSequent, ctx), _ => None).map { scSteps =>
            val scProof = lisa.kernel.proof.SCProof(scSteps, justificationsSeq.map(_.sequentAsKernel))
            env.mkTheorem(newSequent, scProof, justificationsSeq)
          }
        case _ => throw new Error
      }
    }

    // Map[this_hypothesis_formula_index, that_conclusion_formula_index] (left and right)
    // RenamingContext(that_symbol -> this_symbol)
    final def compose(map: Map[Int, (Rule, Map[Int, Int], Map[Int, Int], RenamingContext)]): CompoundRule = {
      val composed = map.map { case (hypothesisIndex, (rule, formulaMappingLeft, formulaMappingRight, renamingContext)) =>
        require(hypotheses.indices.contains(hypothesisIndex))
        val hypothesis = hypotheses(hypothesisIndex)
        // `rule` is allowed to produce unused formulas
        require(formulaMappingLeft.size == hypothesis.left.size && formulaMappingRight.size == hypothesis.right.size)
        require(formulaMappingLeft.values.forall(rule.conclusion.left.indices.contains) &&
          formulaMappingRight.values.forall(rule.conclusion.right.indices.contains))
        def rename(f: Formula): Formula =
          renameSchemas(f, renamingContext.functions, renamingContext.predicates, renamingContext.connectors, renamingContext.variables)
        def renameSequent(s: PartialSequent): PartialSequent =
          s.copy(left = s.left.map(rename), right = s.right.map(rename))
        val renamedConclusion = renameSequent(rule.conclusion)
        // TODO would it be safe to call isSame here? Probably not it seems
        require(formulaMappingLeft.forall { case (i, j) => hypothesis.left(i) == renamedConclusion.left(j) } &&
          formulaMappingRight.forall { case (i, j) => hypothesis.right(i) == renamedConclusion.right(j) })
        val renamedHypotheses = rule.hypotheses.map(renameSequent)

        hypothesisIndex -> (???, renamedHypotheses)
      }
      val newHypotheses = hypotheses.zipWithIndex.flatMap { case (originalSequent, i) =>
        composed.get(i).map { case (_, sequent) => sequent }.getOrElse(IndexedSeq(originalSequent))
      }
      val newReconstruct: ReconstructRule = (bot, ctx) => {
        val thisSteps = reconstruct(bot, ctx)
        val ttt = hypotheses.zipWithIndex.map { case (hypothesis, i) =>
          composed.get(i)
        }
        //SCSubproof()
        // TODO extract unifyAllFormulas into a separate function

        ???
      }
      CompoundRule(newHypotheses, conclusion, ???)
    }
  }

  class RuleIntroduction(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule
  class RuleElimination(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

  given Conversion[Rule, RuleTactic] = _()

  case class CompoundRule private[RuleDefinitions](override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

}