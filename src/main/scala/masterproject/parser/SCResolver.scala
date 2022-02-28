package masterproject.parser

import lisa.kernel.fol.FOL
import masterproject.parser.SCParsed.*
import lisa.kernel.fol.FOL.*

import scala.util.parsing.input.Position

object SCResolver {

  private sealed abstract class TreeType
  private case object TypeFormula extends TreeType
  private case object TypeTerm extends TreeType

  case class ResolutionException(message: String, pos: Position) extends Exception(s"$message:\n${pos.longString}")

  private def throwTypeError(expected: TreeType, actual: TreeType, pos: Position): Nothing =
    throw ResolutionException(s"Type error: expected $expected, got $actual", pos)

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
      FunctionTerm(resolveFunctionTermLabel(name, 0), Seq.empty)
    case SCParsedApplication(name, args) =>
      FunctionTerm(resolveFunctionTermLabel(name, args.size), args.map(resolveTerm(_)))
    case _ => throwTypeError(TypeTerm, TypeFormula, tree.pos)
  }

  private def resolveFormula(tree: SCParsedTermOrFormula)(implicit ctx: ScopedContext): Formula = tree match {
    case name: SCParsedName =>
      PredicateFormula(resolvePredicateFormulaLabel(name, 0), Seq.empty)
    case SCParsedApplication(name, args) =>
      PredicateFormula(resolvePredicateFormulaLabel(name, args.size), args.map(resolveTerm(_)))
    case operator: SCParsedBinaryOperator =>
      val label: Either[PredicateLabel, ConnectorLabel] = operator match {
        case _: SCParsedAnd => Right(And)
        case _: SCParsedOr => Right(Or)
        case _: SCParsedImplies => Right(Implies)
        case _: SCParsedIff => Right(Iff)
        case _: SCParsedEqual => Left(equality)
      }
      val args = Seq(operator.left, operator.right)
      label match {
        case Left(label) => PredicateFormula(label, args.map(resolveTerm(_)))
        case Right(label) => ConnectorFormula(label, args.map(resolveFormula(_)))
      }
    case SCParsedNot(termOrFormula) =>
      ConnectorFormula(Neg, Seq(resolveFormula(termOrFormula)))
    case binder: SCParsedBinder =>
      if(ctx.variables.contains(binder.bound)) {
        throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
      }
      val label = binder match {
        case _: SCParsedForall => Forall
        case _: SCParsedExists => Exists
        case _: SCParsedExistsOne => ExistsOne
      }
      BinderFormula(label, VariableLabel(binder.bound), resolveFormula(binder.termOrFormula)(ctx.copy(variables = ctx.variables + binder.bound)))
  }

  def resolveTopLevelFormula(tree: SCParsedTermOrFormula): Formula =
    resolveFormula(tree)(ScopedContext(variables = Set.empty))

}
