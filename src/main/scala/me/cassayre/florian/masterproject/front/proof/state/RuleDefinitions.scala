package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.proof.SequentCalculus.{SCProofStep, SCSubproof}
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.unification.UnificationUtils

import scala.collection.View

trait RuleDefinitions extends ProofEnvironmentDefinitions with UnificationUtils {

  type ReconstructRule = PartialFunction[(lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext), IndexedSeq[SCProofStep]]
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

  protected def applyRuleInference(
    parameters: RuleParameters,
    patternsFrom: IndexedSeq[PartialSequent],
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {
    def parametersView: View[IndexedSeq[SequentSelector]] =
      if(patternsFrom.size == valuesFrom.size) {
        matchIndices(parameters.selectors, patternsFrom, valuesFrom)
      } else {
        View.empty
      }

    parametersView.flatMap { selectors =>
      val ctx = UnificationContext(parameters.predicates.map(r => r.schema -> r.lambda).toMap, parameters.functions.map(r => r.schema -> r.lambda).toMap, parameters.connectors.map(r => r.schema -> r.lambda).toMap, parameters.variables)
      unifyAndResolve(patternsFrom, valuesFrom, patternsTo, ctx, selectors)
    }.headOption
  }

  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleParameters) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
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

  sealed abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

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
      applyRuleInference(parameters, hypotheses, IndexedSeq(conclusion), topSequents).flatMap {
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
