package masterproject.parser

import masterproject.parser.SCParsed.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.Sequent

import scala.util.parsing.input.Position

object SCResolver {

  // This procedure cannot differentiate variables and functions of arity 0.
  // In this case for now it assumes they are variables.

  case class ResolutionException(message: String, pos: Position) extends Exception(s"$message:\n${pos.longString}")

  case class ScopedContext(variables: Set[String])

  private def resolveFunctionTermLabel(name: SCParsedName, arity: Int): FunctionLabel = name match {
    case SCParsedConstant(identifier) => ConstantFunctionLabel(identifier, arity)
    case SCParsedSchema(identifier) => SchematicFunctionLabel(identifier, arity)
  }

  private def resolvePredicateFormulaLabel(name: SCParsedName, arity: Int): PredicateLabel = name match {
    case SCParsedConstant(identifier) => ConstantPredicateLabel(identifier, arity)
    case SCParsedSchema(identifier) => SchematicPredicateLabel(identifier, arity)
  }

  private def resolveTerm(tree: SCParsedTermOrFormula)(implicit ctx: ScopedContext): Term = tree match {
    case name: SCParsedName =>
      VariableTerm(VariableLabel(name.identifier)) // Ambiguous: could be a function as well!
    case SCParsedApplication(name, args) =>
      FunctionTerm(resolveFunctionTermLabel(name, args.size), args.map(resolveTerm(_)))
    case product: SCParsedProduct =>
      val name = product match {
        case _: SCParsedOrderedPair => "ordered_pair"
        case _: SCParsedSet2 => "unordered_pair"
      }
      FunctionTerm(ConstantFunctionLabel(name, 2), Seq(product.left, product.right).map(resolveTerm(_)))
    case SCParsedSet1(subtree) =>
      FunctionTerm(ConstantFunctionLabel("singleton", 1), Seq(resolveTerm(subtree)))
    case SCParsedSet0 =>
      FunctionTerm(ConstantFunctionLabel("empty_set", 0), Seq.empty)
    case SCParsedPower(subtree) =>
      FunctionTerm(ConstantFunctionLabel("power_set", 1), Seq(resolveTerm(subtree)))
    case SCParsedUnion(subtree) =>
      FunctionTerm(ConstantFunctionLabel("union", 1), Seq(resolveTerm(subtree)))
    case _ => throw ResolutionException("Type error: expected term, got formula", tree.pos)
  }

  private def resolveFormulaContext(tree: SCParsedTermOrFormula)(implicit ctx: ScopedContext): Formula = tree match {
    case name: SCParsedName =>
      PredicateFormula(resolvePredicateFormulaLabel(name, 0), Seq.empty)
    case SCParsedApplication(name, args) =>
      PredicateFormula(resolvePredicateFormulaLabel(name, args.size), args.map(resolveTerm(_)))
    case operator: SCParsedBinaryOperator =>
      val label: Either[PredicateLabel, ConnectorLabel] = operator match {
        case _: SCParsedEqual => Left(equality)
        case _: SCParsedMembership => Left(ConstantPredicateLabel("set_membership", 2))
        case _: SCParsedSubset => Left(ConstantPredicateLabel("subset_of", 2))
        case _: SCParsedSameCardinality => Left(ConstantPredicateLabel("same_cardinality", 2))
        case _: SCParsedAnd => Right(And)
        case _: SCParsedOr => Right(Or)
        case _: SCParsedImplies => Right(Implies)
        case _: SCParsedIff => Right(Iff)
      }
      val args = Seq(operator.left, operator.right)
      label match {
        case Left(label) => PredicateFormula(label, args.map(resolveTerm(_)))
        case Right(label) => ConnectorFormula(label, args.map(resolveFormulaContext(_)))
      }
    case SCParsedNot(termOrFormula) =>
      ConnectorFormula(Neg, Seq(resolveFormulaContext(termOrFormula)))
    case binder: SCParsedBinder =>
      binder.bound.find(ctx.variables.contains).orElse(binder.bound.diff(binder.bound.distinct).headOption) match {
        case Some(bound) => throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
        case None => ()
      }
      val label = binder match {
        case _: SCParsedForall => Forall
        case _: SCParsedExists => Exists
        case _: SCParsedExistsOne => ExistsOne
      }
      binder.bound.foldRight(resolveFormulaContext(binder.termOrFormula)(ctx.copy(variables = ctx.variables ++ binder.bound)))(
        (bound, body) => BinderFormula(label, VariableLabel(bound), body)
      )
    case _ => throw ResolutionException("Type error: expected formula, got term", tree.pos)
  }

  def resolveFormula(tree: SCParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(ScopedContext(variables = Set.empty))
    
  def resolveSequent(tree: SCParsedSequent): Sequent =
    Sequent(tree.left.map(resolveFormula).toSet, tree.right.map(resolveFormula).toSet)

}
