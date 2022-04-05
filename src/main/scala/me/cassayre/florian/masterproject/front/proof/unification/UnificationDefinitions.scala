package me.cassayre.florian.masterproject.front.proof.unification

import me.cassayre.florian.masterproject.front.fol.FOL.*

trait UnificationDefinitions {

  private case class ScopedUnificationContext(variables: Map[VariableLabel, VariableLabel]) {
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): ScopedUnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
  }
  private val emptyScopedUnificationContext = ScopedUnificationContext(Map.empty)

  // TODO we should store information about which bound variables are in scope to avoid name clashes
  case class UnificationContext(
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])],
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])],
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])],
    variables: Map[VariableLabel, VariableLabel], // TODO enforce uniqueness in pattern
  ) {
    def withPredicate(pattern: SchematicPredicateLabel[0], target: Formula): UnificationContext =
      copy(predicates = predicates + (pattern -> (target, Seq.empty)))
    def withFunction(pattern: SchematicFunctionLabel[0], target: Term): UnificationContext =
      copy(functions = functions + (pattern -> (target, Seq.empty)))
    def withPredicate(pattern: SchematicPredicateLabel[?], target: Formula, args: Seq[VariableLabel]): UnificationContext =
      copy(predicates = predicates + (pattern -> (target, args)))
    def withFunction(pattern: SchematicFunctionLabel[?], target: Term, args: Seq[VariableLabel]): UnificationContext =
      copy(functions = functions + (pattern -> (target, args)))
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): UnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
    def apply(predicate: SchematicPredicateLabel[0]): Formula = predicates(predicate)._1
    def apply(function: SchematicFunctionLabel[0]): Term = functions(function)._1
    def apply(variable: VariableLabel): VariableLabel = variables(variable)
    def applyMultiary(function: SchematicFunctionLabel[?]): (Term, Seq[VariableLabel]) = functions(function)
    def applyMultiary(predicate: SchematicPredicateLabel[?]): (Formula, Seq[VariableLabel]) = predicates(predicate)
    def applyMultiary(connector: SchematicConnectorLabel[?]): (Formula, Seq[SchematicPredicateLabel[0]]) = connectors(connector)
    def apply[N <: Arity](function: SchematicFunctionLabel[N])(args: FillArgs[Term, N]): Term = {
      val (body, argsSeq) = functions(function)
      substituteVariables(body, argsSeq.zip(args.toSeq).toMap)
    }
    def apply[N <: Arity](predicate: SchematicPredicateLabel[N])(args: FillArgs[Term, N]): Formula = {
      val (body, argsSeq) = predicates(predicate)
      substituteVariables(body, argsSeq.zip(args.toSeq).toMap)
    }
    def apply[N <: Arity](connector: SchematicConnectorLabel[N])(args: FillArgs[Formula, N]): Formula = {
      val (body, argsSeq) = connectors(connector)
      instantiatePredicateSchemas(body, argsSeq.zip(args.toSeq.map(_ -> Seq.empty)).toMap)
    }
  }
  private val emptyUnificationContext = UnificationContext(Map.empty, Map.empty, Map.empty, Map.empty)

  case class RenamingContext(
    predicates: Map[SchematicPredicateLabel[?], SchematicPredicateLabel[?]],
    functions: Map[SchematicFunctionLabel[?], SchematicFunctionLabel[?]],
    connectors: Map[SchematicConnectorLabel[?], SchematicConnectorLabel[?]],
    variables: Map[VariableLabel, VariableLabel],
  )
  val emptyRenamingContext: RenamingContext = RenamingContext(Map.empty, Map.empty, Map.empty, Map.empty)

}
