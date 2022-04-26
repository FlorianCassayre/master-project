package me.cassayre.florian.masterproject.front.fol.utils

import me.cassayre.florian.masterproject.front.fol.conversions.to.FormulaConversionsTo
import me.cassayre.florian.masterproject.front.fol.definitions.FormulaDefinitions
import me.cassayre.florian.masterproject.front.fol.ops.CommonOps

trait FormulaUtils extends TermUtils {
  this: FormulaDefinitions & FormulaConversionsTo & CommonOps =>

  case class LambdaPredicate[N <: Arity] private(parameters: Seq[SchematicFunctionLabel[0]], body: Formula) extends LambdaDefinition[N, SchematicFunctionLabel[0], Formula]
  object LambdaPredicate {
    def apply[N <: Arity](f: FillArgs[SchematicFunctionLabel[0], N] => Formula)(using v: ValueOf[N]): LambdaPredicate[N] = {
      val n = v.value
      val dummyVariable = SchematicFunctionLabel[0]("")
      val taken = schematicFunctionsOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicFunctionLabel.apply[0](_), n, f, taken)
      new LambdaPredicate(params.toSeq, body)
    }
    def unsafe(parameters: Seq[SchematicFunctionLabel[0]], body: Formula): LambdaPredicate[?] = new LambdaPredicate(parameters, body)
  }

  case class InstantiatedPredicate private(schema: SchematicPredicateLabel[?], lambda: LambdaPredicate[?])
    extends InstantiatedSchema[SchematicPredicateLabel[?], Formula, SchematicFunctionLabel[0]]
  object InstantiatedPredicate {
    def apply[N <: Arity](schema: SchematicPredicateLabel[N], lambda: LambdaPredicate[N])(using v: ValueOf[N]): InstantiatedPredicate = new InstantiatedPredicate(schema, lambda)
    def unsafe(schema: SchematicPredicateLabel[?], lambda: LambdaPredicate[?]): InstantiatedPredicate = new InstantiatedPredicate(schema, lambda)
  }

  case class LambdaConnector[N <: Arity] private(parameters: Seq[SchematicPredicateLabel[0]], body: Formula) extends LambdaDefinition[N, SchematicPredicateLabel[0], Formula]
  object LambdaConnector {
    def apply[N <: Arity](f: FillArgs[SchematicPredicateLabel[0], N] => Formula)(using v: ValueOf[N]): LambdaConnector[N] = {
      val n = v.value
      val dummyVariable = SchematicPredicateLabel[0]("")
      val taken = schematicPredicatesOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicPredicateLabel.apply[0](_), n, f, taken)
      new LambdaConnector(params.toSeq, body)
    }
    def unsafe(parameters: Seq[SchematicPredicateLabel[0]], body: Formula): LambdaConnector[?] = new LambdaConnector(parameters, body)
  }

  case class InstantiatedConnector private(schema: SchematicConnectorLabel[?], lambda: LambdaConnector[?])
    extends InstantiatedSchema[SchematicConnectorLabel[?], Formula, SchematicPredicateLabel[0]]
  object InstantiatedConnector {
    def apply[N <: Arity](schema: SchematicConnectorLabel[N], lambda: LambdaConnector[N])(using v: ValueOf[N]): InstantiatedConnector = new InstantiatedConnector(schema, lambda)
    def unsafe(schema: SchematicConnectorLabel[?], lambda: LambdaConnector[?]): InstantiatedConnector = new InstantiatedConnector(schema, lambda)
  }


  def freshId(taken: Set[String], base: String): String = {
    def findFirst(i: Int): String = {
      val id = s"${base}_$i"
      if(taken.contains(id)) findFirst(i + 1) else id
    }
    findFirst(0)
  }

  def freshIds(taken: Set[String], n: Int, base: String = "x"): Seq[String] = {
    require(n >= 0)
    def findMany(i: Int, n: Int, taken: Set[String], acc: Seq[String]): Seq[String] = {
      if(n > 0) {
        val id = s"${base}_$i"
        if(taken.contains(id)) findMany(i + 1, n, taken, acc) else findMany(i + 1, n - 1, taken + id, id +: acc)
      } else {
        acc
      }
    }
    findMany(0, n, taken, Seq.empty).reverse
  }

  def adaptConnectorSchemas(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] = {
    def recursive(formula: Formula, predicates: Set[SchematicPredicateLabel[?]], translation: Map[ConnectorFormula, SchematicPredicateLabel[?]]):
    (Formula, Set[SchematicPredicateLabel[?]], Map[ConnectorFormula, SchematicPredicateLabel[?]]) = formula match {
      case other: PredicateFormula => (other, predicates, translation)
      case connector @ ConnectorFormula(label, args) =>
        label match {
          case schematic: SchematicConnectorLabel[?] =>
            translation.get(connector) match {
              case Some(predicate) => (PredicateFormula.unsafe(predicate, Seq.empty), predicates, translation)
              case None =>
                val newId = freshId(predicates.map(_.id), schematic.id)
                val newLabel = SchematicPredicateLabel[0](newId)
                (PredicateFormula.unsafe(newLabel, Seq.empty), predicates + newLabel, translation + (connector -> newLabel))
            }
          case _ =>
            val (newFormulas, newAllPredicates, newAllTranslation) = args.foldLeft((Seq.empty[Formula], predicates, translation)) {
              case ((acc, accPredicates, accTranslation), arg) =>
                val (newFormula, np, nt) = recursive(arg, accPredicates, accTranslation)
                (acc :+ newFormula, np, nt)
            }
            (ConnectorFormula.unsafe(label, newFormulas), newAllPredicates, newAllTranslation)
        }
      case BinderFormula(label, bound, inner) =>
        val (newInner, newPredicates, newTranslation) = recursive(inner, predicates, translation)
        (BinderFormula(label, bound, newInner), newPredicates, newTranslation)
    }
    val schematicPredicates = formulas.flatMap(schematicPredicatesOf).toSet
    val (translatedFormulas, _, _) = formulas.foldLeft((IndexedSeq.empty[Formula], schematicPredicates, Map.empty[ConnectorFormula, SchematicPredicateLabel[?]])) {
      case ((acc, taken, currentTranslation), formula) =>
        val (translatedFormula, newTaken, newTranslation) = recursive(formula, taken, currentTranslation)
        (acc :+ translatedFormula, newTaken, newTranslation)
    }
    translatedFormulas
  }

  def isSame(f1: Formula, f2: Formula): Boolean =
    adaptConnectorSchemas(IndexedSeq(f1, f2)) match {
      case IndexedSeq(af1, af2) =>
        lisa.kernel.fol.FOL.isSame(af1, af2)
      case e => throw new MatchError(e)
    }

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

  def schematicFunctionsOf(formula: Formula): Set[SchematicFunctionLabel[?]] =
    functionsOf(formula).collect { case schematic: SchematicFunctionLabel[?] => schematic }

  def predicatesOf(formula: Formula): Set[PredicateLabel[?]] = formula match {
    case PredicateFormula(label, _) => Set(label)
    case ConnectorFormula(_, args) => args.flatMap(predicatesOf).toSet
    case BinderFormula(_, _, inner) => predicatesOf(inner)
  }

  def schematicPredicatesOf(formula: Formula): Set[SchematicPredicateLabel[?]] =
    predicatesOf(formula).collect { case schematic: SchematicPredicateLabel[?] => schematic }

  def schematicConnectorsOf(formula: Formula): Set[SchematicConnectorLabel[?]] = formula match {
    case PredicateFormula(_, _) => Set.empty
    case ConnectorFormula(label, args) =>
      val set = label match {
        case _: ConstantConnectorLabel[?] => Set.empty
        case schematic: SchematicConnectorLabel[?] => Set(schematic)
      }
      set ++ args.flatMap(schematicConnectorsOf)
    case BinderFormula(_, _, inner) => schematicConnectorsOf(inner)
  }

  def declaredBoundVariablesOf(formula: Formula): Set[VariableLabel] = formula match {
    case PredicateFormula(_, args) => Set.empty
    case ConnectorFormula(_, args) => args.flatMap(declaredBoundVariablesOf).toSet
    case BinderFormula(_, bound, inner) => declaredBoundVariablesOf(inner) + bound
  }


  protected def isFormulaWellFormed(formula: Formula)(using ctx: Scope): Boolean = formula match {
    case PredicateFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isWellFormed)
    case ConnectorFormula(_: SchematicConnectorLabel[?], Seq()) => false // Use nullary predicates instead
    case ConnectorFormula(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isFormulaWellFormed)
    case BinderFormula(label, bound, inner) =>
      !ctx.boundVariables.contains(bound) && isFormulaWellFormed(inner)(using ctx.copy(boundVariables = ctx.boundVariables + bound))
  }

  def isWellFormed(formula: Formula): Boolean = isFormulaWellFormed(formula)(using Scope())


  def substituteVariables(formula: Formula, map: Map[VariableLabel, Term]): Formula = formula match {
    case PredicateFormula(label, args) => PredicateFormula.unsafe(label, args.map(substituteVariables(_, map)))
    case ConnectorFormula(label, args) => ConnectorFormula.unsafe(label, args.map(substituteVariables(_, map)))
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
      case PredicateFormula(label, args) => PredicateFormula.unsafe(label, args.map(instantiateFunctionSchemasInternal(_, map)))
      case ConnectorFormula(label, args) => ConnectorFormula.unsafe(label, args.map(instantiateFunctionSchemasInternal(_, map)))
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

  def instantiateFunctionSchemas(formula: Formula, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Formula = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateFunctionSchemasInternal(formula, map)
  }

  private def instantiatePredicateSchemasInternal(formula: Formula, map: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])]): Formula = {
    formula match {
      case PredicateFormula(label, args) =>
        val option = label match {
          case schematic: SchematicPredicateLabel[?] => map.get(schematic)
          case _ => None
        }
        option match {
          case Some((r, a)) => substituteVariables(r, a.zip(args).toMap)
          case None => formula
        }
      case ConnectorFormula(label, args) => ConnectorFormula.unsafe(label, args.map(instantiatePredicateSchemasInternal(_, map)))
      case BinderFormula(label, bound, inner) =>
        val fv = freeVariablesOf(formula) -- map.flatMap { case (_, (_, a)) => a }
        if (fv.contains(bound)) {
          val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
          val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
          BinderFormula(label, newBoundVariable, instantiatePredicateSchemasInternal(newInner, map))
        } else {
          BinderFormula(label, bound, instantiatePredicateSchemasInternal(inner, map))
        }
    }
  }

  def instantiatePredicateSchemas(formula: Formula, map: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])]): Formula = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiatePredicateSchemasInternal(formula, map)
  }

  private def instantiateConnectorSchemasInternal(formula: Formula, map: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])]): Formula = formula match {
    case PredicateFormula(_, _) => formula
    case ConnectorFormula(label, args) =>
      val option = label match {
        case schematic: SchematicConnectorLabel[?] => map.get(schematic)
        case _: ConstantConnectorLabel[?] => None
      }
      option match {
        case Some((f, a)) =>
          assert(a.size == args.size)
          instantiatePredicateSchemas(f, a.zip(args).map { case (k, v) => k -> (v, Seq.empty) }.toMap)
        case None =>
          ConnectorFormula.unsafe(label, args.map(instantiateConnectorSchemasInternal(_, map)))
      }
    case BinderFormula(label, bound, inner) => BinderFormula(label, bound, instantiateConnectorSchemasInternal(inner, map))
  }

  def instantiateConnectorSchemas(formula: Formula, map: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])]): Formula = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateConnectorSchemasInternal(formula, map)
  }

  // TODO carefully check that variable capture is handled properly in all cases
  private def instantiateSchemasInternal(
    formula: Formula,
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])],
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])],
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])]
  ): Formula = formula match {
    case PredicateFormula(label, args) =>
      label match {
        case schematic: SchematicPredicateLabel[?] if predicates.contains(schematic) =>
          val (r, a) = predicates(schematic)
          substituteVariables(r, a.zip(args).toMap)
        case _ =>
          PredicateFormula.unsafe(label, args.map(instantiateFunctionSchemasInternal(_, functions)))
      }
    case ConnectorFormula(label, args) =>
      label match {
        case schematic: SchematicConnectorLabel[?] if connectors.contains(schematic) =>
          val (r, a) = connectors(schematic)
          instantiatePredicateSchemas(r, a.zip(args).map { case (k, v) => k -> (v, Seq.empty) }.toMap)
        case _ =>
          ConnectorFormula.unsafe(label, args.map(instantiateSchemasInternal(_, functions, predicates, connectors)))
      }
    case BinderFormula(label, bound, inner) =>
      val fv = functions.values.map(_._1).flatMap(freeVariablesOf).toSet ++
        predicates.values.map(_._1).flatMap(freeVariablesOf).toSet ++
        connectors.values.map(_._1).flatMap(freeVariablesOf).toSet
      if (fv.contains(bound)) {
        val newBoundVariable = VariableLabel(freshId(fv.map(_.id), bound.id))
        val newInner = substituteVariables(inner, Map(bound -> VariableTerm(newBoundVariable)))
        BinderFormula(label, newBoundVariable, instantiateSchemasInternal(newInner, functions, predicates, connectors))
      } else {
        BinderFormula(label, bound, instantiateSchemasInternal(inner, functions, predicates, connectors))
      }
  }

  def instantiateSchemas(
    formula: Formula,
    functions: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])],
    predicates: Map[SchematicPredicateLabel[?], (Formula, Seq[VariableLabel])],
    connectors: Map[SchematicConnectorLabel[?], (Formula, Seq[SchematicPredicateLabel[0]])]
  ): Formula = {
    require(functions.forall { case (f, (_, args)) => f.arity == args.size })
    require(predicates.forall { case (f, (_, args)) => f.arity == args.size })
    require(connectors.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateSchemasInternal(formula, functions, predicates, connectors)
  }

  def renameSchemas(
    formula: Formula,
    functionsMap: Map[SchematicFunctionLabel[?], FunctionLabel[?]],
    predicatesMap: Map[SchematicPredicateLabel[?], PredicateLabel[?]],
    connectorsMap: Map[SchematicConnectorLabel[?], ConnectorLabel[?]],
    variablesMap: Map[VariableLabel, VariableLabel],
    termsMap: Map[SchematicFunctionLabel[0], Term],
    formulasMap: Map[SchematicPredicateLabel[0], Formula],
  ): Formula = formula match {
    case PredicateFormula(label, args) =>
      val result = label match {
        case schema: SchematicPredicateLabel[?] =>
          if(schema.arity == 0) {
            val schema0 = schema.asInstanceOf[SchematicPredicateLabel[0]]
            formulasMap.get(schema0).map(Right.apply).getOrElse(Left(predicatesMap.getOrElse(schema, label)))
          } else {
            Left(predicatesMap.getOrElse(schema, label))
          }
        case _ => Left(label)
      }
      result match {
        case Left(newLabel) => PredicateFormula.unsafe(newLabel, args.map(renameSchemas(_, functionsMap, variablesMap, termsMap)))
        case Right(newFormula) => newFormula
      }
    case ConnectorFormula(label, args) =>
      val newLabel = label match {
        case schema: SchematicConnectorLabel[?] if connectorsMap.contains(schema) => connectorsMap(schema)
        case _ => label
      }
      ConnectorFormula.unsafe(label, args.map(renameSchemas(_, functionsMap, predicatesMap, connectorsMap, variablesMap, termsMap, formulasMap)))
    case BinderFormula(label, bound, inner) =>
      val newBound = variablesMap.getOrElse(bound, bound)
      BinderFormula(label, newBound, renameSchemas(inner, functionsMap, predicatesMap, connectorsMap, variablesMap, termsMap, formulasMap))
  }

  def fillTupleParametersPredicate[N <: Arity](n: N, f: FillArgs[VariableLabel, N] => Formula): (FillArgs[VariableLabel, N], Formula) = {
    val dummyVariable = VariableLabel("")
    val dummyFormula = fillTupleParameters(_ => dummyVariable, n, f)._2
    val taken = (freeVariablesOf(dummyFormula) ++ declaredBoundVariablesOf(dummyFormula)).map(_.id)
    fillTupleParameters(VariableLabel.apply, n, f, taken)
  }

  def fillTupleParametersConnector[N <: Arity](n: N, f: FillArgs[SchematicPredicateLabel[0], N] => Formula): (FillArgs[SchematicPredicateLabel[0], N], Formula) = {
    val dummyPredicate = SchematicPredicateLabel[0]("")
    val taken = schematicPredicatesOf(fillTupleParameters(_ => dummyPredicate, n, f)._2).map(_.id)
    fillTupleParameters(SchematicPredicateLabel[0](_), n, f, taken)
  }

}
