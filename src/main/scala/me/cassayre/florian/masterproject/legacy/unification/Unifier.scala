package me.cassayre.florian.masterproject.legacy.unification

import utilities.Printer
import me.cassayre.florian.masterproject.front.fol.FOL.*

import scala.annotation.tailrec

object Unifier {

  private case class ScopedUnificationContext(variables: Map[VariableLabel, VariableLabel]) {
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): ScopedUnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
  }
  private val emptyScopedUnificationContext = ScopedUnificationContext(Map.empty)

  // TODO we should store information about which bound variables are in scope to avoid name clashes
  case class UnificationContext(
    predicates: Map[SchematicPredicateLabel[?], LambdaPredicate[?]],
    functions: Map[SchematicFunctionLabel[?], LambdaFunction[?]],
    connectors: Map[SchematicConnectorLabel[?], LambdaConnector[?]],
    variables: Map[VariableLabel, VariableLabel], // TODO enforce uniqueness in pattern
  ) {
    def withPredicate(pattern: SchematicPredicateLabel[0], target: Formula): UnificationContext =
      copy(predicates = predicates + (pattern -> LambdaPredicate.unsafe(Seq.empty, target)))
    def withFunction(pattern: SchematicFunctionLabel[0], target: Term): UnificationContext =
      copy(functions = functions + (pattern -> LambdaFunction.unsafe(Seq.empty, target)))
    def withPredicate(pattern: SchematicPredicateLabel[?], target: Formula, args: Seq[SchematicFunctionLabel[0]]): UnificationContext =
      copy(predicates = predicates + (pattern -> LambdaPredicate.unsafe(args, target)))
    def withFunction(pattern: SchematicFunctionLabel[?], target: Term, args: Seq[SchematicFunctionLabel[0]]): UnificationContext =
      copy(functions = functions + (pattern -> LambdaFunction.unsafe(args, target)))
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): UnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
    def apply(predicate: SchematicPredicateLabel[0]): Formula = predicates(predicate).body
    def apply(function: SchematicFunctionLabel[0]): Term = functions(function).body
    def apply(variable: VariableLabel): VariableLabel = variables(variable)
    def applyMultiary(function: SchematicFunctionLabel[?]): LambdaFunction[?] = functions(function)
    def applyMultiary(predicate: SchematicPredicateLabel[?]): LambdaPredicate[?] = predicates(predicate)
    def applyMultiary(connector: SchematicConnectorLabel[?]): LambdaConnector[?] = connectors(connector)
    def apply[N <: Arity](function: SchematicFunctionLabel[N]): LambdaFunction[N] = functions(function).asInstanceOf[LambdaFunction[N]]
    def apply[N <: Arity](predicate: SchematicPredicateLabel[N]): LambdaPredicate[N] = predicates(predicate).asInstanceOf[LambdaPredicate[N]]
    def apply[N <: Arity](connector: SchematicConnectorLabel[N]): LambdaConnector[N] = connectors(connector).asInstanceOf[LambdaConnector[N]]
    def assignedPredicates: Seq[AssignedPredicate] = predicates.map { case (k, v) => AssignedPredicate.unsafe(k, v) }.toSeq
    def assignedFunctions: Seq[AssignedFunction] = functions.map { case (k, v) => AssignedFunction.unsafe(k, v) }.toSeq
    def assignedConnectors: Seq[AssignedConnector] = connectors.map { case (k, v) => AssignedConnector.unsafe(k, v) }.toSeq
  }
  private val emptyUnificationContext = UnificationContext(Map.empty, Map.empty, Map.empty, Map.empty)

  case class RenamingContext(
    predicates: Map[SchematicPredicateLabel[?], SchematicPredicateLabel[?]],
    functions: Map[SchematicFunctionLabel[?], SchematicFunctionLabel[?]],
    connectors: Map[SchematicConnectorLabel[?], SchematicConnectorLabel[?]],
    variables: Map[VariableLabel, VariableLabel],
  )
  val emptyRenamingContext: RenamingContext = RenamingContext(Map.empty, Map.empty, Map.empty, Map.empty)

  sealed abstract class UnificationResult {
    // This is not really needed for now
    /*def map(f: UnificationContext => UnificationContext): UnificationResult = this match {
      case UnificationSuccess(ctx) => UnificationSuccess(f(ctx))
      case failure: UnificationFailure => failure
    }
    def flatMap(f: UnificationContext => UnificationResult): UnificationResult = this match {
      case UnificationSuccess(ctx) => f(ctx)
      case failure: UnificationFailure => failure
    }*/
  }
  case class UnificationSuccess(ctx: UnificationContext) extends UnificationResult
  case class UnificationFailure(message: String) extends UnificationResult


  // TODO
  private def isSame(f1: Formula, f2: Formula): Boolean = f1 == f2
  private def isSame(t1: Term, t2: Term): Boolean = t1 == t2


  // This function has the useful property that it will avoid performing needless computations
  // It assumes that the formulas/terms are well-formed
  private def unifyZip[T](f: (T, T, UnificationContext) => UnificationResult, patterns: Seq[T], targets: Seq[T], ctx: UnificationContext): UnificationResult = {
    @tailrec
    def unifyZipRecursive(pattern: Seq[T], target: Seq[T], acc: UnificationContext): UnificationResult = (pattern, target) match {
      case (patternHead +: patternTail, targetHead +: targetTail) =>
        f(patternHead, targetHead, acc) match {
          case success: UnificationSuccess => unifyZipRecursive(patternTail, targetTail, success.ctx)
          case failure: UnificationFailure => failure // Early stopping
        }
      case (Seq(), Seq()) => UnificationSuccess(acc)
      case _ => throw new Exception
    }
    unifyZipRecursive(patterns, targets, ctx)
  }

  private def unifyTerms(pattern: Term, target: Term, ctx: UnificationContext)(implicit scopedCtx: ScopedUnificationContext): UnificationResult = (pattern, target) match {
    case (VariableTerm(patternLabel), VariableTerm(targetLabel)) =>
      // This should be safe since we assumed all variables were bound
      val expectedVariable = scopedCtx.variables(patternLabel)
      if(targetLabel == expectedVariable) {
        UnificationSuccess(ctx)
      } else {
        UnificationFailure(s"Bound variables do not match, expected ${expectedVariable.id} got ${targetLabel.id}")
      }
    case (FunctionTerm(patternLabel: ConstantFunctionLabel[?], patternArgs), FunctionTerm(targetLabel: ConstantFunctionLabel[?], targetArgs)) =>
      if(patternLabel == targetLabel) {
        unifyZip(unifyTerms(_, _, _), patternArgs, targetArgs, ctx)
      } else {
        UnificationFailure(s"Function labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case (FunctionTerm(patternSchematic: SchematicFunctionLabel[?], patternArgs), _) =>
      patternSchematic match {
        case SchematicFunctionLabel(_, 0) =>
          val nullaryLabel = patternSchematic.asInstanceOf[SchematicFunctionLabel[0]]
          ctx.functions.get(nullaryLabel) match {
            case Some(LambdaFunction(_, expectedTarget)) =>
              if (isSame(target, expectedTarget)) {
                UnificationSuccess(ctx)
              } else {
                UnificationFailure(s"Schematic function failed to unify, expected ${Printer.prettyTerm(expectedTarget)} got ${Printer.prettyTerm(target)}")
              }
            case None =>
              UnificationSuccess(ctx.withFunction(nullaryLabel, target))
          }
        case SchematicFunctionLabel(_, _) =>
          UnificationFailure(s"Nonzero-ary function schema in pattern: ${patternSchematic.id}")
      }
    case _ =>
      def typeName(t: Term): String = t match {
        case _: VariableTerm => "Variable"
        case _: FunctionTerm => "Function"
      }
      UnificationFailure(s"Types do not match, expected ${typeName(pattern).toLowerCase} got ${typeName(target).toLowerCase}")
  }
  private def unifyFormulas(pattern: Formula, target: Formula, ctx: UnificationContext)(implicit scopedCtx: ScopedUnificationContext): UnificationResult = (pattern, target) match {
    case (PredicateFormula(patternLabel: ConstantPredicateLabel[?], patternArgs), PredicateFormula(targetLabel: ConstantPredicateLabel[?], targetArgs)) =>
      if(patternLabel == targetLabel) {
        unifyZip(unifyTerms(_, _, _), patternArgs, targetArgs, ctx)
      } else {
        UnificationFailure(s"Predicate labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case (PredicateFormula(patternSchematic: SchematicPredicateLabel[?], patternArgs), _) =>
      patternSchematic match {
        case SchematicPredicateLabel(_, 0) =>
          val nullaryLabel = patternSchematic.asInstanceOf[SchematicPredicateLabel[0]]
          ctx.predicates.get(nullaryLabel) match {
            case Some(LambdaPredicate(_, expectedTarget)) =>
              if(isSame(target, expectedTarget)) {
                UnificationSuccess(ctx)
              } else {
                UnificationFailure(s"Schematic predicate failed to unify, expected ${Printer.prettyFormula(expectedTarget)} got ${Printer.prettyFormula(target)}")
              }
            case None =>
              UnificationSuccess(ctx.withPredicate(nullaryLabel, target))
          }
        case SchematicPredicateLabel(_, _) =>
          UnificationFailure(s"Nonzero-ary predicate schema in pattern: ${patternSchematic.id}")
      }
    case (ConnectorFormula(patternLabel, patternArgs), ConnectorFormula(targetLabel, targetArgs)) =>
      if(patternLabel == targetLabel) {
        unifyZip(unifyFormulas(_, _, _), patternArgs, targetArgs, ctx)
      } else {
        UnificationFailure(s"Connector labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case (BinderFormula(patternLabel, patternBound, patternInner), BinderFormula(targetLabel, targetBound, targetInner)) =>
      if(patternLabel == targetLabel) {
        unifyFormulas(patternInner, targetInner, ctx.withVariable(patternBound, targetBound))(scopedCtx.withVariable(patternBound, targetBound))
      } else {
        UnificationFailure(s"Binder labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case _ =>
      def typeName(f: Formula): String = f match {
        case _: PredicateFormula => "Predicate"
        case _: ConnectorFormula => "Connector"
        case _: BinderFormula => "Binder"
      }
      UnificationFailure(s"Types do not match, expected ${typeName(pattern).toLowerCase} got ${typeName(target).toLowerCase}")
  }

  // TODO rename these and add `ctx` as parameter
  def unify(pattern: Term, target: Term): UnificationResult =
    unifyTerms(pattern, target, emptyUnificationContext)(emptyScopedUnificationContext)
  def unify(pattern: Formula, target: Formula): UnificationResult =
    unifyFormulas(pattern, target, emptyUnificationContext)(emptyScopedUnificationContext)

  def unifyAllTerms(patterns: Seq[Term], targets: Seq[Term], ctx: UnificationContext = emptyUnificationContext): UnificationResult =
    unifyZip[Term](unifyTerms(_, _, _)(emptyScopedUnificationContext), patterns, targets, ctx)
  def unifyAllFormulas(patterns: Seq[Formula], targets: Seq[Formula], ctx: UnificationContext = emptyUnificationContext): UnificationResult =
    unifyZip[Formula](unifyFormulas(_, _, _)(emptyScopedUnificationContext), patterns, targets, ctx)


  private def reverseUnificationFormulas(substitutionMap: Map[PredicateLabel[0], Formula], target: Formula): Formula =
    substitutionMap.toSeq.filter { case (_, f) => isSame(f, target) } match {
      case Seq() =>
        target match {
          case _: PredicateFormula => target
          case ConnectorFormula(label, args) => ConnectorFormula.unsafe(label, args.map(reverseUnificationFormulas(substitutionMap, _)))
          case BinderFormula(label, bound, inner) => BinderFormula(label, bound, reverseUnificationFormulas(substitutionMap, inner))
        }
      case Seq((label, _)) =>
        assert(label.arity == 0)
        PredicateFormula.unsafe(label, Seq.empty)
      case _ => // Multiple
        throw new Exception
    }

  def reverseUnification(substitutionMap: Map[PredicateLabel[0], Formula], target: Formula): Formula = {
    require(substitutionMap.values.forall(_.freeVariables.isEmpty)) // Should not have free variables
    reverseUnificationFormulas(substitutionMap, target)
  }

  def instantiateFormulaFromContext(formula: Formula, ctx: UnificationContext): Formula =
    instantiateFormulaSchemas(
      formula,
      functions = ctx.assignedFunctions,
      predicates = ctx.assignedPredicates,
      connectors = ctx.assignedConnectors,
    )

}
