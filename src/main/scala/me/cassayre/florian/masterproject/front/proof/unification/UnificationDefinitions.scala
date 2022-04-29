package me.cassayre.florian.masterproject.front.proof.unification

import me.cassayre.florian.masterproject.front.fol.FOL.*

trait UnificationDefinitions {

  private case class ScopedUnificationContext(variables: Map[VariableLabel, VariableLabel] = Map.empty) {
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): ScopedUnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
  }

  case class UnificationContext(
    predicates: Map[SchematicPredicateLabel[?], LambdaPredicate[?]] = Map.empty,
    functions: Map[SchematicFunctionLabel[?], LambdaFunction[?]] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], LambdaConnector[?]] = Map.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  ) {
    def +(predicate: AssignedPredicate): UnificationContext = copy(predicates = predicates + (predicate.schema -> predicate.lambda))
    def +(function: AssignedFunction): UnificationContext = copy(functions = functions + (function.schema -> function.lambda))
    def +(connector: AssignedConnector): UnificationContext = copy(connectors = connectors + (connector.schema -> connector.lambda))
    def +(pair: (VariableLabel, VariableLabel)): UnificationContext = copy(variables = variables + pair)

    def apply[N <: Arity](predicate: SchematicPredicateLabel[N]): LambdaPredicate[N] = predicates(predicate).asInstanceOf[LambdaPredicate[N]]
    def apply[N <: Arity](function: SchematicFunctionLabel[N]): LambdaFunction[N] = functions(function).asInstanceOf[LambdaFunction[N]]
    def apply[N <: Arity](connector: SchematicConnectorLabel[N]): LambdaConnector[N] = connectors(connector).asInstanceOf[LambdaConnector[N]]
    def apply(variable: VariableLabel): VariableLabel = variables(variable)

    def assignedPredicates: Seq[AssignedPredicate] = predicates.map { case (k, v) => AssignedPredicate.unsafe(k, v) }.toSeq
    def assignedFunctions: Seq[AssignedFunction] = functions.map { case (k, v) => AssignedFunction.unsafe(k, v) }.toSeq
    def assignedConnectors: Seq[AssignedConnector] = connectors.map { case (k, v) => AssignedConnector.unsafe(k, v) }.toSeq
  }

  case class RenamingContext(
    predicates: Seq[RenamedPredicateSchema] = Seq.empty,
    functions: Seq[RenamedFunctionSchema] = Seq.empty,
    connectors: Seq[RenamedConnectorSchema] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  )

}
