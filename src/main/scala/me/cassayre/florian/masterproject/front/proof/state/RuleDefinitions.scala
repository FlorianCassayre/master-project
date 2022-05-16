package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.{SCProofStep, SCSubproof}
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.unification.UnificationUtils

import scala.collection.View

trait RuleDefinitions extends ProofEnvironmentDefinitions with UnificationUtils {

  type ReconstructRule = PartialFunction[(lisa.kernel.proof.SequentCalculus.Sequent, UnificationContext), IndexedSeq[SCProofStep]]

  case class RuleParameters(
    selectors: Map[Int, SequentSelector] = Map.empty,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
    resolutions: Map[Int, Either[Sequent, Justified]] = Map.empty,
    resolutionsSelectors: Map[Int, (IndexedSeq[Int], IndexedSeq[Int])] = Map.empty,
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

    def withVariable(label: VariableLabel, value: VariableLabel): RuleParameters =
      copy(variables = variables + (label -> value))

    def withResolution(i: Int, sequent: Sequent): RuleParameters =
      copy(resolutions = resolutions + (i -> Left(sequent)))
    def withResolution(i: Int, justified: Justified): RuleParameters =
      copy(resolutions = resolutions + (i -> Right(justified)))
  }
  object RuleParameters {
    def apply(args: (AssignedFunction | AssignedPredicate | AssignedConnector | (VariableLabel, VariableLabel))*): RuleParameters =
      args.foldLeft(new RuleParameters())((acc, e) => e match {
        case assigned: AssignedFunction => acc.copy(functions = acc.functions :+ assigned)
        case assigned: AssignedPredicate => acc.copy(predicates = acc.predicates :+ assigned)
        case assigned: AssignedConnector => acc.copy(connectors = acc.connectors :+ assigned)
        case pair @ (_: VariableLabel, _: VariableLabel) => acc.copy(variables = acc.variables + pair)
      })
  }

  protected def applyRuleInference(
    parameters: RuleParameters,
    patternsFrom: IndexedSeq[PartialSequent],
    patternsTo: IndexedSeq[PartialSequent],
    valuesFrom: IndexedSeq[Sequent],
    valuesTo: IndexedSeq[Option[Sequent]],
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {
    def parametersView: View[(IndexedSeq[SequentSelector], IndexedSeq[Option[SequentSelector]])] =
      if(patternsFrom.size == valuesFrom.size && patternsTo.size == valuesTo.size) {
        matchIndices(parameters.selectors, parameters.resolutionsSelectors, patternsFrom, patternsTo, valuesFrom, valuesTo)
      } else {
        View.empty
      }

    lazy val ctx = UnificationContext(
      parameters.predicates.map(r => r.schema -> r.lambda).toMap,
      parameters.functions.map(r => r.schema -> r.lambda).toMap,
      parameters.connectors.map(r => r.schema -> r.lambda).toMap,
      parameters.variables
    )

    lazy val (newPatternsFrom, newValuesFrom, nonEmptyValuesTo) = {
      val (nonEmptyValuesTo, indices) = valuesTo.zipWithIndex.collect { case (Some(value), i) => (value, i) }.unzip
      (patternsFrom ++ indices.map(patternsTo),
        valuesFrom ++ nonEmptyValuesTo,
        nonEmptyValuesTo)
    }

    parametersView.flatMap { case (selectorsFrom, selectorsTo) =>
      val newSelectors = selectorsFrom ++ selectorsTo.flatten
      unifyAndResolve(newPatternsFrom, newValuesFrom, patternsTo, ctx, newSelectors).flatMap {
        case (solvedValues, resultCtx) =>
          val (actualValuesTo, rightValues) = solvedValues.splitAt(valuesTo.size)
          if(rightValues.zip(nonEmptyValuesTo).forall { case (unified, target) => isSameSequent(unified, target) }) {
            Some((actualValuesTo, resultCtx))
          } else {
            None
          }
      }
    }.headOption
  }

  case class RuleTactic private[RuleDefinitions](rule: Rule, parameters: RuleParameters) extends TacticGoalFunctionalPruning {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Either[Sequent, Justified]], ReconstructSteps)] = {
      if(parameters.resolutions.keySet.subsetOf(rule.hypotheses.indices.toSet)) {
        val resolutions = parameters.resolutions.view.mapValues {
          case Left(sequent) => sequent
          case Right(justified) => justified.sequent
        }.toMap
        val knownHypotheses = rule.hypotheses.indices.map(resolutions.get)
        applyRuleInference(parameters, IndexedSeq(rule.conclusion), rule.hypotheses, IndexedSeq(proofGoal), knownHypotheses).flatMap {
          case (newGoals, ctx) =>
            val stepsOption = rule.reconstruct.andThen(Some.apply).applyOrElse((proofGoal, ctx), _ => None)
            val rewrites = resolutions.exists { case (i, sequent) => sequent != newGoals(i) }
            stepsOption.map { steps =>
              val reconstruction =
                if(rewrites) {
                  val indices = newGoals.indices.map(-_ - 1)
                  () => IndexedSeq(SCSubproof( // TODO one level is normally sufficient
                    SCProof(
                      IndexedSeq(SCSubproof(
                        SCProof(steps, newGoals.map(sequentToKernel)),
                        indices,
                      )),
                      newGoals.indices.map(i => resolutions.getOrElse(i, newGoals(i))).map(sequentToKernel)),
                    indices,
                  ))
                } else {
                  () => steps
                }
              (newGoals.indices.map(i => parameters.resolutions.getOrElse(i, Left(newGoals(i)))), reconstruction)
            }
        }
      } else {
        None
      }
    }

    override def toString: String = s"${rule.getClass.getSimpleName}(...)"
  }

  sealed abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    def reconstruct: ReconstructRule

    require(isLegalPatterns(hypotheses) && isLegalPatterns(IndexedSeq(conclusion)))

    final def apply(parameters: RuleParameters = RuleParameters()): RuleTactic =
      RuleTactic(this, parameters)

    final def apply(justification0: Justified, rest: Justified*): Option[Theorem] =
      apply(RuleParameters())((justification0 +: rest)*)(using justification0.environment)
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
      require(parameters.resolutions.keySet.forall(_ == 0))
      val resolutionOpt = parameters.resolutions.get(0).map {
        case Left(sequent) => sequent
        case Right(justified) => justified.sequent // Why would anyone do that? Anyway, we should support it
      }
      applyRuleInference(parameters, hypotheses, IndexedSeq(conclusion), topSequents, IndexedSeq(resolutionOpt)).flatMap {
        case (IndexedSeq(newSequent), ctx) =>
          reconstruct.andThen(Some.apply).applyOrElse((newSequent, ctx), _ => None).map { scSteps =>
            val scProof = lisa.kernel.proof.SCProof(scSteps, justificationsSeq.map(_.sequentAsKernel))
            env.mkTheorem(newSequent, scProof, justificationsSeq)
          }
        case _ => throw new Error
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

  open class RuleBase(override val hypotheses: IndexedSeq[PartialSequent], override val conclusion: PartialSequent, override val reconstruct: ReconstructRule) extends Rule

  given Conversion[Rule, RuleTactic] = _()

}
