package masterproject.front

import lisa.kernel.Printer
import lisa.kernel.fol.FOL.*

import scala.annotation.tailrec

object Unification {

  private case class ScopedUnificationContext(variables: Map[VariableLabel, VariableLabel]) {
    def withVariable(patternVariable: VariableLabel, targetVariable: VariableLabel): ScopedUnificationContext =
      copy(variables = variables + (patternVariable -> targetVariable))
  }
  private val emptyScopedUnificationContext = ScopedUnificationContext(Map.empty)

  // TODO we should store information about which bound variables are in scope to avoid name clashes
  case class UnificationContext(
                                 predicates: Map[SchematicPredicateLabel, Formula],
                                 functions: Map[SchematicFunctionLabel, Term],
                               ) {
    def withPredicate(pattern: SchematicPredicateLabel, target: Formula): UnificationContext =
      copy(predicates = predicates + (pattern -> target))
    def withFunction(pattern: SchematicFunctionLabel, target: Term): UnificationContext =
      copy(functions = functions + (pattern -> target))
  }
  private val emptyUnificationContext = UnificationContext(Map.empty, Map.empty)

  sealed abstract class UnificationResult {
    def map(f: UnificationContext => UnificationContext): UnificationResult = this match {
      case UnificationSuccess(ctx) => UnificationSuccess(f(ctx))
      case failure: UnificationFailure => failure
    }
    def flatMap(f: UnificationContext => UnificationResult): UnificationResult = this match {
      case UnificationSuccess(ctx) => f(ctx)
      case failure: UnificationFailure => failure
    }
  }
  case class UnificationSuccess(ctx: UnificationContext) extends UnificationResult
  case class UnificationFailure(message: String) extends UnificationResult


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
    case (FunctionTerm(patternLabel: ConstantFunctionLabel, patternArgs), FunctionTerm(targetLabel: ConstantFunctionLabel, targetArgs)) =>
      if(patternLabel == targetLabel) {
        unifyZip(unifyTerms(_, _, _), patternArgs, targetArgs, ctx)
      } else {
        UnificationFailure(s"Function labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case (FunctionTerm(patternSchematic: SchematicFunctionLabel, patternArgs), _) =>
      if(patternSchematic.arity == 0) {
        ctx.functions.get(patternSchematic) match {
          case Some(expectedTarget) =>
            if(isSame(target, expectedTarget)) {
              UnificationSuccess(ctx)
            } else {
              UnificationFailure(s"Schematic function failed to unify, expected ${Printer.prettyTerm(expectedTarget)} got ${Printer.prettyTerm(target)}")
            }
          case None =>
            UnificationSuccess(ctx.withFunction(patternSchematic, target))
        }
      } else {
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
    case (PredicateFormula(patternLabel: ConstantPredicateLabel, patternArgs), PredicateFormula(targetLabel: ConstantPredicateLabel, targetArgs)) =>
      if(patternLabel == targetLabel) {
        unifyZip(unifyTerms(_, _, _), patternArgs, targetArgs, ctx)
      } else {
        UnificationFailure(s"Predicate labels do not match, expected ${patternLabel.id} got ${targetLabel.id}")
      }
    case (PredicateFormula(patternSchematic: SchematicPredicateLabel, patternArgs), _) =>
      if(patternSchematic.arity == 0) {
        ctx.predicates.get(patternSchematic) match {
          case Some(expectedTarget) =>
            if(isSame(target, expectedTarget)) {
              UnificationSuccess(ctx)
            } else {
              UnificationFailure(s"Schematic predicate failed to unify, expected ${Printer.prettyFormula(expectedTarget)} got ${Printer.prettyFormula(target)}")
            }
          case None =>
            UnificationSuccess(ctx.withPredicate(patternSchematic, target))
        }
      } else {
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
        unifyFormulas(patternInner, targetInner, ctx)(scopedCtx.withVariable(patternBound, targetBound))
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

  def unify(pattern: Term, target: Term): UnificationResult =
    unifyTerms(pattern, target, emptyUnificationContext)(emptyScopedUnificationContext)
  def unify(pattern: Formula, target: Formula): UnificationResult =
    unifyFormulas(pattern, target, emptyUnificationContext)(emptyScopedUnificationContext)

  def unifyAllTerms(patterns: Seq[Term], targets: Seq[Term]): UnificationResult =
    unifyZip[Term](unifyTerms(_, _, _)(emptyScopedUnificationContext), patterns, targets, emptyUnificationContext)
  def unifyAllFormulas(patterns: Seq[Formula], targets: Seq[Formula]): UnificationResult =
    unifyZip[Formula](unifyFormulas(_, _, _)(emptyScopedUnificationContext), patterns, targets, emptyUnificationContext)

}
