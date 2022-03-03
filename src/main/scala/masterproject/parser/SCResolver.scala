package masterproject.parser

import masterproject.parser.SCParsed.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent
import masterproject.parser.ReadingException.ResolutionException

import scala.util.parsing.input.Position

private[parser] object SCResolver {

  // This procedure cannot differentiate variables and functions of arity 0.
  // In this case for now it assumes they are variables.

  case class ScopedContext(variables: Set[String])

  private def resolveFunctionTermLabel(name: ParsedName, arity: Int): FunctionLabel = name match {
    case ParsedConstant(identifier) => ConstantFunctionLabel(identifier, arity)
    case ParsedSchema(identifier) => SchematicFunctionLabel(identifier, arity)
  }

  private def resolvePredicateFormulaLabel(name: ParsedName, arity: Int): PredicateLabel = name match {
    case ParsedConstant(identifier) => ConstantPredicateLabel(identifier, arity)
    case ParsedSchema(identifier) => SchematicPredicateLabel(identifier, arity)
  }

  private def resolveTerm(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Term = tree match {
    case name: ParsedName =>
      VariableTerm(VariableLabel(name.identifier)) // Ambiguous: could be a function as well!
    case ParsedApplication(name, args) =>
      FunctionTerm(resolveFunctionTermLabel(name, args.size), args.map(resolveTerm(_)))
    case product: ParsedProduct =>
      val name = product match {
        case _: ParsedOrderedPair => "ordered_pair"
        case _: ParsedSet2 => "unordered_pair"
      }
      FunctionTerm(ConstantFunctionLabel(name, 2), Seq(product.left, product.right).map(resolveTerm(_)))
    case ParsedSet1(subtree) =>
      FunctionTerm(ConstantFunctionLabel("singleton", 1), Seq(resolveTerm(subtree)))
    case ParsedSet0() =>
      FunctionTerm(ConstantFunctionLabel("empty_set", 0), Seq.empty)
    case ParsedPower(subtree) =>
      FunctionTerm(ConstantFunctionLabel("power_set", 1), Seq(resolveTerm(subtree)))
    case ParsedUnion(subtree) =>
      FunctionTerm(ConstantFunctionLabel("union", 1), Seq(resolveTerm(subtree)))
    case _ => throw ResolutionException("Type error: expected term, got formula", tree.pos)
  }

  private def resolveFormulaContext(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Formula = tree match {
    case name: ParsedName =>
      PredicateFormula(resolvePredicateFormulaLabel(name, 0), Seq.empty)
    case ParsedApplication(name, args) =>
      PredicateFormula(resolvePredicateFormulaLabel(name, args.size), args.map(resolveTerm(_)))
    case operator: ParsedBinaryOperator =>
      val label: Either[PredicateLabel, ConnectorLabel] = operator match {
        case _: ParsedEqual => Left(equality)
        case _: ParsedMembership => Left(ConstantPredicateLabel("set_membership", 2))
        case _: ParsedSubset => Left(ConstantPredicateLabel("subset_of", 2))
        case _: ParsedSameCardinality => Left(ConstantPredicateLabel("same_cardinality", 2))
        case _: ParsedAnd => Right(And)
        case _: ParsedOr => Right(Or)
        case _: ParsedImplies => Right(Implies)
        case _: ParsedIff => Right(Iff)
      }
      val args = Seq(operator.left, operator.right)
      label match {
        case Left(label) => PredicateFormula(label, args.map(resolveTerm(_)))
        case Right(label) => ConnectorFormula(label, args.map(resolveFormulaContext(_)))
      }
    case ParsedNot(termOrFormula) =>
      ConnectorFormula(Neg, Seq(resolveFormulaContext(termOrFormula)))
    case binder: ParsedBinder =>
      binder.bound.find(ctx.variables.contains).orElse(binder.bound.diff(binder.bound.distinct).headOption) match {
        case Some(bound) => throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
        case None => ()
      }
      val label = binder match {
        case _: ParsedForall => Forall
        case _: ParsedExists => Exists
        case _: ParsedExistsOne => ExistsOne
      }
      binder.bound.foldRight(resolveFormulaContext(binder.termOrFormula)(ctx.copy(variables = ctx.variables ++ binder.bound)))(
        (bound, body) => BinderFormula(label, VariableLabel(bound), body)
      )
    case _ => throw ResolutionException("Type error: expected formula, got term", tree.pos)
  }

  def resolveFormula(tree: ParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(ScopedContext(variables = Set.empty))

  def resolveSequent(tree: ParsedSequent): Sequent =
    Sequent(tree.left.map(resolveFormula).toSet, tree.right.map(resolveFormula).toSet)

}
