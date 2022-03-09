package masterproject.front.fol.utils

import masterproject.front.fol.definitions.FormulaDefinitions

trait FormulaUtils extends TermUtils {
  this: FormulaDefinitions =>

  def freeVariablesOf(formula: Formula): Set[VariableLabel] = formula match {
    case PredicateFormula(_, args) => args.flatMap(freeVariablesOf).toSet
    case ConnectorFormula(_, args) => args.flatMap(freeVariablesOf).toSet
    case BinderFormula(_, bound, inner) => freeVariablesOf(inner) - bound
  }

  def functionsOf(formula: Formula): Set[FunctionLabel[?]] = formula match {
    case PredicateFormula(_, args) => args.flatMap(functionsOf).toSet
    case ConnectorFormula(_, args) => args.flatMap(functionsOf).toSet
    case BinderFormula(_, _, inner) => functionsOf(inner)
  }

  def predicatesOf(formula: Formula): Set[PredicateLabel[?]] = formula match {
    case PredicateFormula(label, _) => Set(label)
    case ConnectorFormula(_, args) => args.flatMap(predicatesOf).toSet
    case BinderFormula(_, _, inner) => predicatesOf(inner)
  }


  protected def isFormulaWellFormed(formula: Formula)(implicit ctx: Scope): Boolean = formula match {
    case PredicateFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isTermWellFormed(_))
    case ConnectorFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isFormulaWellFormed(_))
    case BinderFormula(label, bound, inner) =>
      !ctx.boundVariables.contains(bound) && isFormulaWellFormed(inner)(ctx.copy(boundVariables = ctx.boundVariables + bound))
  }

  def isWellFormed(formula: Formula): Boolean = isFormulaWellFormed(formula)(Scope())


  def freshId(taken: Set[String], base: String): String = {
    def findFirst(i: Int): String = {
      val id = s"${base}_$i"
      if(taken.contains(id)) findFirst(i + 1) else id
    }
    findFirst(0)
  }

  def substituteVariables(formula: Formula, map: Map[VariableLabel, Term]): Formula = formula match {
    case PredicateFormula(label, args) => PredicateFormula(label, args.map(substituteVariables(_, map)))
    case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(substituteVariables(_, map)))
    case BinderFormula(label, bound, inner) =>
      val newSubst = map - bound
      val fv = map.values.flatMap(freeVariablesOf).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
        val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
        BinderFormula(label, newBoundVariable, substituteVariables(newInner, newSubst))
      } else {
        BinderFormula(label, bound, substituteVariables(inner, newSubst))
      }
  }

  protected def instantiateFunctionSchemasInternal(formula: Formula, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Formula = {
    formula match {
      case PredicateFormula(label, args) => PredicateFormula(label, args.map(instantiateFunctionSchemasInternal(_, map)))
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiateFunctionSchemasInternal(_, map)))
      case BinderFormula(label, bound, inner) =>
        val fv = map.flatMap { case (f, (r, args)) => freeVariablesOf(r) -- args.toSet }.toSet
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiateFunctionSchemasInternal(newInner, map))
        } else {
          BinderFormula(label, bound, instantiateFunctionSchemasInternal(inner, map))
        }
    }
  }

  private def instantiateFunctionSchemas(formula: Formula, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Formula = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateFunctionSchemasInternal(formula, map)
  }

  private def instantiatePredicateSchema(formula: Formula, map: Map[SchematicPredicateLabel[?], (Term, Seq[VariableLabel])]): Formula = {
    formula match {
      case PredicateFormula(label, args) =>
        val option = label match {
          case schematic: SchematicPredicateLabel[?] => map.get(schematic)
          case _ => None
        }
        option match {
          case Some((r, a)) => substituteVariables(formula, a.zip(args).toMap)
          case None => formula
        }
      case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(instantiatePredicateSchema(_, map)))
      case BinderFormula(label, bound, inner) =>
        val fv = freeVariablesOf(formula) -- map.flatMap { case (_, (_, a)) => a }
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiatePredicateSchema(newInner, map))
        } else {
          BinderFormula(label, bound, instantiatePredicateSchema(inner, map))
        }
    }
  }

}
