package me.cassayre.florian.masterproject.front.proof.unification

import me.cassayre.florian.masterproject.front.proof.sequent.SequentDefinitions
import me.cassayre.florian.masterproject.front.fol.FOL.*

trait UnificationUtils extends UnificationDefinitions with SequentDefinitions {

  def isLegalPatterns(patterns: IndexedSeq[PartialSequent]): Boolean = {
    lazy val boundVariables = patterns.flatMap(declaredBoundVariablesOfSequent)

    // Applications match arity, no clashing bound variable patterns
    lazy val noMalformedFormulas = patterns.forall(isSequentWellFormed)
    // Declared variable patterns must have a globally unique name
    lazy val noClashingBoundVariablePatterns = boundVariables.distinct.size == boundVariables.size
    // Free variables should not reuse a name of a bound variable
    lazy val noConflictingBoundFreeVariables = boundVariables.intersect(patterns.flatMap(freeVariablesOfSequent)).isEmpty

    noMalformedFormulas && noClashingBoundVariablePatterns && noConflictingBoundFreeVariables
  }

  private type Constraints = Seq[Constraint]
  private type ConstraintsResult = Option[Constraints]

  private type Context = Set[(VariableLabel, VariableLabel)]

  private enum Constraint {
    case SchematicFunction(label: SchematicFunctionLabel[?], args: Seq[Term], value: Term, ctx: Context)
    case SchematicPredicate(label: SchematicPredicateLabel[?], args: Seq[Term], value: Formula, ctx: Context)
    case SchematicConnector(label: SchematicConnectorLabel[?], args: Seq[Formula], value: Formula, ctx: Context)
    case Variable(pattern: VariableLabel, value: VariableLabel)
  }
  import Constraint.*

  private def collect(patternsAndValues: IndexedSeq[(Formula, Formula)]): ConstraintsResult = {
    val empty: ConstraintsResult = Some(Seq.empty)
    def merge(o1: ConstraintsResult, o2: ConstraintsResult): ConstraintsResult =
      for {
        c1 <- o1
        c2 <- o2
      } yield c1 ++ c2

    def collectRecursiveTerm(pattern: Term, value: Term)(using ctx: Context): ConstraintsResult = (pattern, value) match {
      case (FunctionTerm(labelPattern: ConstantFunctionLabel[?], argsPattern), FunctionTerm(labelValue: ConstantFunctionLabel[?], argsValue)) if labelPattern == labelValue =>
        argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveTerm(argPattern, argValue) }.fold(empty)(merge)
      case (FunctionTerm(labelPattern: SchematicFunctionLabel[?], argsPattern), _) =>
        Some(Seq(SchematicFunction(labelPattern, argsPattern, value, ctx)))
      case (VariableTerm(labelPattern), VariableTerm(labelValue)) =>
        if(ctx.contains((labelPattern, labelValue))) { // Bound variable
          Some(Seq(Variable(labelPattern, labelValue)))
        } else if(ctx.forall { case (p, v) => p != labelPattern && v != labelValue }) { // Free variable
          Some(Seq(Variable(labelPattern, labelValue))) // TODO merge these branches
        } else {
          None
        }
      case _ => None
    }
    def collectRecursiveFormula(pattern: Formula, value: Formula)(using ctx: Set[(VariableLabel, VariableLabel)]): ConstraintsResult = (pattern, value) match {
      case (PredicateFormula(labelPattern: ConstantPredicateLabel[?], argsPattern), PredicateFormula(labelValue: ConstantPredicateLabel[?], argsValue)) if labelPattern == labelValue =>
        argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveTerm(argPattern, argValue) }.fold(empty)(merge)
      case (PredicateFormula(labelPattern: SchematicPredicateLabel[?], argsPattern), _) =>
        Some(Seq(SchematicPredicate(labelPattern, argsPattern, value, ctx)))
      case (ConnectorFormula(labelPattern: ConstantConnectorLabel[?], argsPattern), ConnectorFormula(labelValue: ConstantConnectorLabel[?], argsValue)) if labelPattern == labelValue =>
        argsPattern.zip(argsValue).map { case (argPattern, argValue) => collectRecursiveFormula(argPattern, argValue) }.fold(empty)(merge)
      case (ConnectorFormula(labelPattern: SchematicConnectorLabel[?], argsPattern), _) =>
        Some(Seq(SchematicConnector(labelPattern, argsPattern, value, ctx)))
      case (BinderFormula(labelPattern, boundPattern, innerPattern), BinderFormula(labelValue, boundValue, innerValue)) if labelPattern == labelValue =>
        collectRecursiveFormula(innerPattern, innerValue)(using ctx + ((boundPattern, boundValue)))
      case _ => None
    }

    patternsAndValues.map { case (pattern, value) => collectRecursiveFormula(pattern, value)(using Set.empty) }.fold(empty)(merge)
  }

  private def unifyFromConstraints(
    constraints: Constraints,
    partialAssignment: UnificationContext,
    valueFunctions: Set[SchematicFunctionLabel[?]],
    valuePredicates: Set[SchematicPredicateLabel[?]],
    valueConnectors: Set[SchematicConnectorLabel[?]],
    valueVariables: Set[VariableLabel],
  ): Option[UnificationContext] = {
    if(constraints.nonEmpty) {
      def isSolvableTerm(pattern: Term)(using ctx: Set[VariableLabel]): Boolean = pattern match {
        case VariableTerm(label) => /*ctx.contains(label) ||*/ valueVariables.contains(label) // TODO is this correct?
        case FunctionTerm(_: ConstantFunctionLabel[?], args) => args.forall(isSolvableTerm)
        case FunctionTerm(schematic: SchematicFunctionLabel[?], args) => valueFunctions.contains(schematic) && args.forall(isSolvableTerm)
        case _ => false
      }
      def isSolvableFormula(pattern: Formula)(using ctx: Set[VariableLabel]): Boolean = pattern match {
        case PredicateFormula(_: ConstantPredicateLabel[?], args) => args.forall(isSolvableTerm)
        case PredicateFormula(schematic: SchematicPredicateLabel[?], args) => valuePredicates.contains(schematic) && args.forall(isSolvableTerm)
        case ConnectorFormula(_: ConstantConnectorLabel[?], args) => args.forall(isSolvableFormula)
        case ConnectorFormula(schematic: SchematicConnectorLabel[?], args) => valueConnectors.contains(schematic) && args.forall(isSolvableFormula)
        case BinderFormula(_, bound, inner) => valueVariables.contains(bound) && isSolvableFormula(inner)(using ctx + bound)
        case _ => false
      }
      def instantiateTerm(term: Term, assignment: UnificationContext): Term =
        instantiateTermSchemas(unsafeRenameVariables(term, assignment.variables), assignment.assignedFunctions)
      def instantiateFormula(formula: Formula, assignment: UnificationContext): Formula =
        instantiateFormulaSchemas(unsafeRenameVariables(formula, assignment.variables), assignment.assignedFunctions, assignment.assignedPredicates, assignment.assignedConnectors)
      def instantiateConstraint(constraint: Constraint, assignment: UnificationContext): Constraint = constraint match {
        case cse @ SchematicFunction(label, args, value, ctx) => cse.copy(args = args.map(instantiateTerm(_, assignment)))
        case cse @ SchematicPredicate(label, args, value, ctx) => cse.copy(args = args.map(instantiateTerm(_, assignment)))
        case cse @ SchematicConnector(label, args, value, ctx) => cse.copy(args = args.map(instantiateFormula(_, assignment)))
        case _: Variable => constraint // Nothing to do for variables
      }

      // This function tries to factor out all occurrences of `args._2` into `args._1` within `term`, and will store the result in `assignment`
      def greedyFactoringFunction(term: Term, args: IndexedSeq[(SchematicFunctionLabel[0], Term)], assignment: Map[SchematicFunctionLabel[0], Term]): (Term, Map[SchematicFunctionLabel[0], Term]) = {
        args.find { case (_, t) => t == term } match {
          case Some((variable, value)) => (variable, if(!assignment.contains(variable)) assignment + (variable -> value) else assignment)
          case None =>
            term match {
              case _: VariableTerm => (term, assignment)
              case FunctionTerm(label, fArgs) =>
                val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Term], assignment)) { case ((argsAcc, currentAssignment), arg) =>
                  val (newTerm, newAssignment) = greedyFactoringFunction(arg, args, currentAssignment)
                  (argsAcc :+ newTerm, newAssignment)
                }
                (FunctionTerm.unsafe(label, finalArgs), finalAssignment)
            }
        }
      }

      def greedyFactoringPredicate(formula: Formula, args: IndexedSeq[(SchematicFunctionLabel[0], Term)], assignment: Map[SchematicFunctionLabel[0], Term]): (Formula, Map[SchematicFunctionLabel[0], Term]) = {
        formula match {
          case PredicateFormula(label, fArgs) =>
            val (finalAssignment, finalFArgs) = fArgs.foldLeft((assignment, Seq.empty[Term])) { case ((currentAssignment, currentFArgs), a) =>
              val (newA, newAssignment) = greedyFactoringFunction(a, args, currentAssignment)
              (newAssignment, currentFArgs :+ newA)
            }
            (PredicateFormula.unsafe(label, finalFArgs), finalAssignment)
          case ConnectorFormula(label, fArgs) =>
            val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Formula], assignment)) { case ((argsAcc, currentAssignment), arg) =>
              val (newFormula, newAssignment) = greedyFactoringPredicate(arg, args, currentAssignment)
              (argsAcc :+ newFormula, newAssignment)
            }
            (ConnectorFormula.unsafe(label, finalArgs), finalAssignment)
          case BinderFormula(label, bound, inner) => ???
        }
      }

      def greedyFactoringConnector(formula: Formula, args: IndexedSeq[(SchematicPredicateLabel[0], Formula)], assignment: Map[SchematicPredicateLabel[0], Formula]): (Formula, Map[SchematicPredicateLabel[0], Formula]) = {
        args.find { case (_, f) => f == formula } match {
          case Some((variable, value)) => (variable, if(!assignment.contains(variable)) assignment + (variable -> value) else assignment)
          case None =>
            formula match {
              case PredicateFormula(label, fArgs) => (formula, assignment) // Identity
              case ConnectorFormula(label, fArgs) =>
                val (finalArgs, finalAssignment) = fArgs.foldLeft((Seq.empty[Formula], assignment)) { case ((argsAcc, currentAssignment), arg) =>
                  val (newFormula, newAssignment) = greedyFactoringConnector(arg, args, currentAssignment)
                  (argsAcc :+ newFormula, newAssignment)
                }
                (ConnectorFormula.unsafe(label, finalArgs), finalAssignment)
              case BinderFormula(label, bound, inner) => ???
            }
        }
      }

      // The method tries to resolve a constraint and returns two nested options:
      // * None => the constraint is unsolvable (e.g. too many degrees of freedom)
      // * Some(None) => there is a contradiction
      def handler(constraint: Constraint): Option[Option[(Constraints, UnificationContext)]] = constraint match {
        case SchematicFunction(label, args, value, ctx) if args.forall(isSolvableTerm(_)(using ctx.map(_._1))) =>
          // TODO are all bound variables already instantiated?
          // TODO rename args before comparing
          partialAssignment.functions.get(label) match {
            case Some(lambda) =>
              if(isSame(value, lambda.unsafe(args))) {
                Some(Some((IndexedSeq.empty, partialAssignment)))
              } else { // Contradiction with the environment
                Some(None)
              }
            case None =>
              val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
              val freshArguments = freshIds(schematicFunctionsOf(value).map(_.id), valueArgs.size).map(SchematicFunctionLabel.apply[0])
              // We drop the resulting arguments map (because it is not needed anymore)
              val (fBody, _) = greedyFactoringFunction(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
              Some(Some((IndexedSeq.empty, partialAssignment + AssignedFunction.unsafe(label, LambdaFunction.unsafe(freshArguments, fBody)))))
          }
        case SchematicPredicate(label, args, value, ctx) if args.forall(isSolvableTerm(_)(using ctx.map(_._1))) =>
          // Analogous to the above
          partialAssignment.predicates.get(label) match {
            case Some(lambda) =>
              if(isSame(value, lambda.unsafe(args))) {
                Some(Some((IndexedSeq.empty, partialAssignment)))
              } else {
                Some(None)
              }
            case None =>
              val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
              val freshArguments = freshIds(schematicFunctionsOf(value).map(_.id), valueArgs.size).map(SchematicFunctionLabel.apply[0])
              val (fBody, _) = greedyFactoringPredicate(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
              Some(Some((IndexedSeq.empty, partialAssignment + AssignedPredicate.unsafe(label, LambdaPredicate.unsafe(freshArguments, fBody)))))
          }
        case SchematicConnector(label, args, value, ctx) if args.forall(isSolvableFormula(_)(using ctx.map(_._1))) =>
          partialAssignment.connectors.get(label) match {
            case Some(lambda) =>
              if(isSame(value, lambda.unsafe(args))) {
                Some(Some((IndexedSeq.empty, partialAssignment)))
              } else {
                Some(None)
              }
            case None =>
              val valueArgs = args.map(unsafeRenameVariables(_, ctx.toMap))
              val freshArguments = freshIds(schematicPredicatesOf(value).map(_.id), valueArgs.size).map(SchematicPredicateLabel.apply[0])
              val (fBody, _) = greedyFactoringConnector(value, freshArguments.zip(valueArgs).toIndexedSeq, Map.empty)
              Some(Some((IndexedSeq.empty, partialAssignment + AssignedConnector.unsafe(label, LambdaConnector.unsafe(freshArguments, fBody)))))
          }
        case Variable(pattern, value) =>
          if(partialAssignment.variables.forall { case (l, r) => l != pattern || r == value }) {
            Some(Some((IndexedSeq.empty, partialAssignment + (pattern, value))))
          } else {
            Some(None) // Contradiction
          }
        case _ => None
      }
      constraints.view.zipWithIndex.flatMap { case (constraint, i) =>
        handler(constraint).map(_.map { case (newConstraints, newContext) => (newConstraints, newContext, i) })
      }.headOption match {
        case Some(option) => option match {
          case Some((newConstraints, newContext, i)) =>
            def replacement(constraint: Constraint): Constraint = instantiateConstraint(constraint, newContext)
            unifyFromConstraints(constraints.take(i).map(replacement) ++ newConstraints ++ constraints.drop(i + 1).map(replacement), newContext,
              valueFunctions, valuePredicates, valueConnectors, valueVariables)
          case None => None // Explicit error
        }
        case None => None // No available reduction
      }
    } else {
      Some(partialAssignment)
    }
  }

  def unifyAndResolve(
    patterns: IndexedSeq[PartialSequent],
    values: IndexedSeq[Sequent],
    otherPatterns: IndexedSeq[PartialSequent],
    partialAssignment: UnificationContext,
    formulaIndices: IndexedSeq[(IndexedSeq[Int], IndexedSeq[Int])]
  ): Option[(IndexedSeq[Sequent], UnificationContext)] = {

    def schemasOf(sequents: IndexedSeq[SequentBase]):
    (Set[SchematicFunctionLabel[?]], Set[SchematicPredicateLabel[?]], Set[SchematicConnectorLabel[?]], Set[VariableLabel], Set[VariableLabel]) =
      (sequents.flatMap(schematicFunctionsOfSequent).toSet,
        sequents.flatMap(schematicPredicatesOfSequent).toSet,
        sequents.flatMap(schematicConnectorsOfSequent).toSet,
        sequents.flatMap(freeVariablesOfSequent).toSet,
        sequents.flatMap(declaredBoundVariablesOfSequent).toSet)

    val (patternsFunctions, patternsPredicates, patternsConnectors, patternsFreeVariables, patternsBoundVariables) =
      schemasOf(patterns)
    val (valuesFunctions, valuesPredicates, valuesConnectors, valuesFreeVariables, valuesBoundVariables) =
      schemasOf(values)
    val (otherPatternsFunctions, otherPatternsPredicates, otherPatternsConnectors, otherPatternsFreeVariables, otherPatternsBoundVariables) =
      schemasOf(otherPatterns)
    val (partialAssignedFunctions, partialAssignedPredicates, partialAssignedConnectors) =
      (partialAssignment.functions.keySet, partialAssignment.predicates.keySet, partialAssignment.connectors.keySet)
    val (allPatternsFunctions, allPatternsPredicates, allPatternsConnectors, allPatternsFreeVariables, allPatternsBoundVariables) =
      (patternsFunctions ++ otherPatternsFunctions, patternsPredicates ++ otherPatternsPredicates, patternsConnectors ++ otherPatternsConnectors,
        patternsFreeVariables ++ otherPatternsFreeVariables, patternsBoundVariables ++ otherPatternsBoundVariables)
    val valuesVariables = valuesFreeVariables ++ valuesBoundVariables
    val allPatternsVariables = allPatternsFreeVariables ++ allPatternsBoundVariables

    val (nonUnifiableFunctions, nonUnifiablePredicates, nonUnifiableConnectors) =
      (patternsFunctions.diff(otherPatternsFunctions), patternsPredicates.diff(otherPatternsPredicates), patternsConnectors.diff(otherPatternsConnectors))

    lazy val noInvalidSizeRange = patterns.size == values.size && patterns.size == formulaIndices.size && patterns.zip(formulaIndices).zip(values).forall {
      case ((PartialSequent(leftPattern, rightPattern, _, _), (leftIndices, rightIndices)), Sequent(leftValue, rightValue)) =>
        def check(pattern: IndexedSeq[Formula], indices: IndexedSeq[Int], value: IndexedSeq[Formula]): Boolean =
          pattern.size == indices.size && indices.forall(value.indices.contains)
        check(leftPattern, leftIndices, leftValue) && check(rightPattern, rightIndices, rightValue)
    }
    lazy val noMalformedValues = values.forall(isSequentWellFormed)
    lazy val noSchematicConnectorsValues = values.flatMap(schematicConnectorsOfSequent).isEmpty
    lazy val noMalformedAssignment = // TODO some of these should be a contract in `UnificationContext`
      partialAssignment.functions.values.forall(lambda => isWellFormed(lambda.body)) &&
        partialAssignment.predicates.values.forall(lambda => isWellFormed(lambda.body) && schematicConnectorsOf(lambda.body).isEmpty) &&
        partialAssignment.connectors.values.forall(lambda => isWellFormed(lambda.body) && schematicConnectorsOf(lambda.body).isEmpty)
    lazy val noDeclaredUnknown =
      partialAssignedFunctions.subsetOf(allPatternsFunctions) &&
        partialAssignedPredicates.subsetOf(allPatternsPredicates) &&
        partialAssignedConnectors.subsetOf(allPatternsConnectors)
    lazy val noUndeclaredNonUnifiable =
      partialAssignedFunctions.subsetOf(nonUnifiableFunctions) &&
        partialAssignedPredicates.subsetOf(nonUnifiablePredicates) &&
        partialAssignedConnectors.subsetOf(nonUnifiableConnectors)

    val allRequirements =
      isLegalPatterns(patterns) && isLegalPatterns(otherPatterns) &&
        noInvalidSizeRange && noMalformedValues && noSchematicConnectorsValues && noMalformedAssignment &&
        noDeclaredUnknown && noUndeclaredNonUnifiable

    if(allRequirements) {
      // All requirements are satisfied, we can proceed
      // We must rename the symbols in the pattern such that they are distinct from the ones in the values

      // All the names that are already taken (for simplicity we rename everything)
      val initialTakenFunctions: Set[SchematicFunctionLabel[?]] =
        patternsFunctions ++ valuesFunctions ++ otherPatternsFunctions ++
          partialAssignment.functions.values.flatMap { f => schematicFunctionsOf(f.body) } ++
          (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicFunctionsOf(f.body) }
      val initialTakenPredicates: Set[SchematicPredicateLabel[?]] =
        patternsPredicates ++ valuesPredicates ++ otherPatternsPredicates ++
          (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicPredicatesOf(f.body) }
      val initialTakenConnectors: Set[SchematicConnectorLabel[?]] =
        patternsConnectors ++ valuesConnectors ++ otherPatternsConnectors ++
          (partialAssignment.predicates.values ++ partialAssignment.connectors.values).flatMap { f => schematicConnectorsOf(f.body) }
      val initialTakenVariables: Set[VariableLabel] = // Free and bound
        patternsFreeVariables ++ patternsBoundVariables ++
          valuesFreeVariables ++ valuesBoundVariables ++
          otherPatternsFreeVariables ++ otherPatternsBoundVariables ++
          partialAssignment.functions.values.flatMap { lambda => freeVariablesOf(lambda.body) } ++
          partialAssignment.predicates.values.flatMap { lambda => freeVariablesOf(lambda.body) ++ declaredBoundVariablesOf(lambda.body) } ++
          partialAssignment.connectors.values.flatMap { lambda => freeVariablesOf(lambda.body) ++ declaredBoundVariablesOf(lambda.body) }

      def freshMapping[T <: LabelType](taken: Set[T], toRename: Set[T], constructor: (T, String) => T): Map[T, T] = {
        val (finalMap, _) = toRename.foldLeft((Map.empty[T, T], taken.map(_.id))) { case ((map, currentTaken), oldSymbol) =>
          val newName = freshId(currentTaken, oldSymbol.id)
          val newSymbol = constructor(oldSymbol, newName)
          (map + (oldSymbol -> newSymbol), currentTaken + newName)
        }
        finalMap
      }

      // TODO rename variables args

      val functionsFreshMapping = freshMapping(initialTakenFunctions, allPatternsFunctions, (label, newName) => SchematicFunctionLabel.unsafe(newName, label.arity))
      val predicatesFreshMapping = freshMapping(initialTakenPredicates, allPatternsPredicates, (label, newName) => SchematicPredicateLabel.unsafe(newName, label.arity))
      val connectorsFreshMapping = freshMapping(initialTakenConnectors, allPatternsConnectors, (label, newName) => SchematicConnectorLabel.unsafe(newName, label.arity))
      val variablesFreshMapping = freshMapping(initialTakenVariables, allPatternsFreeVariables ++ allPatternsBoundVariables, (_, newName) => VariableLabel(newName))

      val (functionsInverseMapping, predicatesInverseMapping, connectorsInverseMapping, variablesInverseMapping) =
        (functionsFreshMapping.map(_.swap), predicatesFreshMapping.map(_.swap), connectorsFreshMapping.map(_.swap), variablesFreshMapping.map(_.swap))

      def rename(patterns: IndexedSeq[PartialSequent]): IndexedSeq[PartialSequent] = {
        def renameFormulas(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
          formulas.map(f => instantiateFormulaSchemas(
            unsafeRenameVariables(f, variablesFreshMapping),
            functions = functionsFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
            predicates = predicatesFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
            connectors = connectorsFreshMapping.map { case (k, v) => RenamedLabel.unsafe(k, v).toAssignment }.toSeq,
          ))
        patterns.map(p => p.copy(left = renameFormulas(p.left), right = renameFormulas(p.right)))
      }

      val (renamedPatterns, renamedOtherPatterns) = (rename(patterns), rename(otherPatterns))

      val constraints = collect(renamedPatterns.flatMap(_.formulas).zip(values.flatMap(_.formulas)))

      val renamedPartialAssignment = UnificationContext(
        partialAssignment.predicates.map { case (k, v) => predicatesFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.functions.map { case (k, v) => functionsFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.connectors.map { case (k, v) => connectorsFreshMapping.getOrElse(k, k) -> v },
        partialAssignment.variables.map { case (k, v) => variablesFreshMapping.getOrElse(k, k) -> v },
      )

      val unified = constraints
        .flatMap(unifyFromConstraints(_, renamedPartialAssignment, valuesFunctions, valuesPredicates, valuesConnectors, valuesVariables))
        .filter(assignment => // Check if the assignment is full
          assignment.functions.keySet.map(functionsInverseMapping) == allPatternsFunctions &&
            assignment.predicates.keySet.map(predicatesInverseMapping) == allPatternsPredicates &&
            assignment.connectors.keySet.map(connectorsInverseMapping) == allPatternsConnectors &&
            assignment.variables.keySet.map(variablesInverseMapping) == allPatternsVariables
        )

      unified.map { renamedAssignment =>
        val assignment = UnificationContext(
          renamedAssignment.predicates.map { case (k, v) => predicatesInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.functions.map { case (k, v) => functionsInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.connectors.map { case (k, v) => connectorsInverseMapping.getOrElse(k, k) -> v },
          renamedAssignment.variables.map { case (k, v) => variablesInverseMapping.getOrElse(k, k) -> v },
        )

        def removeIndices[T](array: IndexedSeq[T], indices: Seq[Int]): IndexedSeq[T] = {
          val set = indices.toSet
          for {
            (v, i) <- array.zipWithIndex
              if !set.contains(i)
          } yield v
        }

        // Union all
        val (commonLeft, commonRight) = formulaIndices.zip(values).map { case ((indicesLeft, indicesRight), Sequent(valueLeft, valueRight)) =>
          (removeIndices(valueLeft, indicesLeft), removeIndices(valueRight, indicesRight))
        }.reduce { case ((l1, r1), (l2, r2)) =>
          (l1 ++ l2.diff(l1), r1 ++ r2.diff(r1))
        }

        def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
          formulas.map(formula => instantiateFormulaSchemas(unsafeRenameVariables(formula, renamedAssignment.variables),
            renamedAssignment.assignedFunctions, renamedAssignment.assignedPredicates, renamedAssignment.assignedConnectors))

        def createValueTo(common: IndexedSeq[Formula], pattern: IndexedSeq[Formula], partial: Boolean): IndexedSeq[Formula] = {
          val instantiated = instantiate(pattern)
          if(partial) common ++ instantiated else instantiated
        }

        val otherValues = renamedOtherPatterns.map(patterns =>
          Sequent(
            createValueTo(commonLeft, patterns.left, patterns.partialLeft),
            createValueTo(commonRight, patterns.right, patterns.partialRight),
          )
        )

        (otherValues, assignment)
      }
    } else {
      None
    }
  }

}
