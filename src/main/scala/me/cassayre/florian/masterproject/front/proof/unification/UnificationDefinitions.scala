package me.cassayre.florian.masterproject.front.proof.unification

import me.cassayre.florian.masterproject.front.fol.FOL.*

trait UnificationDefinitions {

  case class UnificationContext(
    predicates: Map[SchematicPredicateLabel[?], LambdaPredicate[?]] = Map.empty,
    functions: Map[SchematicFunctionLabel[?], LambdaFunction[?]] = Map.empty,
    connectors: Map[SchematicConnectorLabel[?], LambdaConnector[?]] = Map.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  ) {
    infix def +(predicate: AssignedPredicate): UnificationContext = copy(predicates = predicates + (predicate.schema -> predicate.lambda))
    infix def +(function: AssignedFunction): UnificationContext = copy(functions = functions + (function.schema -> function.lambda))
    infix def +(connector: AssignedConnector): UnificationContext = copy(connectors = connectors + (connector.schema -> connector.lambda))
    infix def +(pair: (VariableLabel, VariableLabel)): UnificationContext = copy(variables = variables + pair)

    def apply[N <: Arity](predicate: SchematicPredicateLabel[N]): LambdaPredicate[N] = predicates(predicate).asInstanceOf[LambdaPredicate[N]]
    def apply[N <: Arity](function: SchematicFunctionLabel[N]): LambdaFunction[N] = functions(function).asInstanceOf[LambdaFunction[N]]
    def apply[N <: Arity](connector: SchematicConnectorLabel[N]): LambdaConnector[N] = connectors(connector).asInstanceOf[LambdaConnector[N]]
    def apply(variable: VariableLabel): VariableLabel = variables(variable)

    def apply(predicate: SchematicPredicateLabel[0]): Formula = predicates(predicate).body
    def apply(function: SchematicFunctionLabel[0]): Term = functions(function).body

    def assignedPredicates: Seq[AssignedPredicate] = predicates.map { case (k, v) => AssignedPredicate.unsafe(k, v) }.toSeq
    def assignedFunctions: Seq[AssignedFunction] = functions.map { case (k, v) => AssignedFunction.unsafe(k, v) }.toSeq
    def assignedConnectors: Seq[AssignedConnector] = connectors.map { case (k, v) => AssignedConnector.unsafe(k, v) }.toSeq

    @deprecated
    def withPredicate(pattern: SchematicPredicateLabel[0], target: Formula): UnificationContext =
      copy(predicates = predicates + (pattern -> LambdaPredicate.unsafe(Seq.empty, target)))
    @deprecated
    def withFunction(pattern: SchematicFunctionLabel[0], target: Term): UnificationContext =
      copy(functions = functions + (pattern -> LambdaFunction.unsafe(Seq.empty, target)))
    @deprecated
    def withPredicate(pattern: SchematicPredicateLabel[?], target: Formula, args: Seq[SchematicFunctionLabel[0]]): UnificationContext =
      copy(predicates = predicates + (pattern -> LambdaPredicate.unsafe(args, target)))
    @deprecated
    def withFunction(pattern: SchematicFunctionLabel[?], target: Term, args: Seq[SchematicFunctionLabel[0]]): UnificationContext =
      copy(functions = functions + (pattern -> LambdaFunction.unsafe(args, target)))
    @deprecated
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): UnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))

    @deprecated
    def applyMultiary(function: SchematicFunctionLabel[?]): LambdaFunction[?] = functions(function)
    @deprecated
    def applyMultiary(predicate: SchematicPredicateLabel[?]): LambdaPredicate[?] = predicates(predicate)
    @deprecated
    def applyMultiary(connector: SchematicConnectorLabel[?]): LambdaConnector[?] = connectors(connector)
  }

  case class RenamingContext(
    predicates: Seq[RenamedPredicateSchema] = Seq.empty,
    functions: Seq[RenamedFunctionSchema] = Seq.empty,
    connectors: Seq[RenamedConnectorSchema] = Seq.empty,
    variables: Map[VariableLabel, VariableLabel] = Map.empty,
  )

}
