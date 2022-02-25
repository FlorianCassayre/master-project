package masterproject.parser

import masterproject.parser.SCParsed.*

import lisa.kernel.fol.FOL.*

import scala.util.parsing.input.Position

object SCResolver {

  // Note that this resolver is naive: type unification only occurs locally
  // This is because it is still to be decided how disambiguations should be represented

  private sealed abstract class TreeType
  private case object TypeFormula extends TreeType
  private case object TypeTerm extends TreeType

  case class ResolutionException(message: String, pos: Position) extends Exception(s"$message:\n${pos.longString}")

  private def throwTypeError(expected: TreeType, actual: TreeType, pos: Position): Nothing =
    throw ResolutionException(s"Type error: expected $expected, got $actual", pos)

  case class ScopedContext(variables: Set[String])

  private def resolveParsedTermOrFormulaInternal(tree: SCParsedTermOrFormula, typeHint: Option[TreeType])(implicit ctx: ScopedContext): Either[Formula, Term] = {
    tree match {
      case name: SCParsedName =>
        val identifier = name.identifier
        val isSchematic = name match {
          case _: SCParsedSchema => true
          case _ => false
        }
        if(!isSchematic && ctx.variables.contains(identifier)) {
          typeHint.foreach { expected =>
            if(expected != TypeTerm) {
              throwTypeError(expected, TypeTerm, tree.pos)
            }
          }
          Right(VariableTerm(VariableLabel(identifier)))
        } else {
          typeHint match {
            case Some(TypeFormula) => Left(PredicateFormula(if(isSchematic) SchematicPredicateLabel(identifier, 0) else ConstantPredicateLabel(identifier, 0), Seq.empty))
            case Some(TypeTerm) => Right(FunctionTerm(if(isSchematic) SchematicFunctionLabel(identifier, 0) else ConstantFunctionLabel(identifier, 0), Seq.empty))
            case None => throw ResolutionException(s"Can't resolve the type of name $identifier", tree.pos)
          }
        }
      case SCParsedApplication(name, args) =>
        val identifier = name.identifier
        if(ctx.variables.contains(identifier)) {
          throw ResolutionException(s"Variables do not take arguments", tree.pos)
        }
        val isSchematic = name match {
          case _: SCParsedSchema => true
          case _ => false
        }
        val arity = args.size
        typeHint match {
          case Some(TypeFormula) =>
            Left(PredicateFormula(
              if(isSchematic) SchematicPredicateLabel(identifier, arity) else ConstantPredicateLabel(identifier, arity),
              args.map(resolveParsedTermOrFormulaInternal(_, Some(TypeTerm)).asInstanceOf[Right[Formula, Term]].value)
            ))
          case Some(TypeTerm) =>
            Right(FunctionTerm(
              if(isSchematic) SchematicFunctionLabel(identifier, arity) else ConstantFunctionLabel(identifier, arity),
              args.map(resolveParsedTermOrFormulaInternal(_, Some(TypeTerm)).asInstanceOf[Right[Formula, Term]].value)
            ))
          case None => throw ResolutionException(s"Can't resolve the type of name $identifier", tree.pos)
        }
      case binary: SCParsedBinaryOperator =>
        typeHint.foreach { expected =>
          if(expected != TypeFormula) {
            throwTypeError(expected, TypeFormula, binary.pos)
          }
        }
        val args = Seq(binary.left, binary.right)
        binary match {
          case connector: (SCParsedAnd | SCParsedOr | SCParsedImplies | SCParsedIff) =>
            val label = connector match {
              case _: SCParsedAnd => And
              case _: SCParsedOr => Or
              case _: SCParsedImplies => Implies
              case _: SCParsedIff => Iff
            }
            Left(ConnectorFormula(label, args.map(resolveParsedTermOrFormulaInternal(_, Some(TypeFormula)).asInstanceOf[Left[Formula, Term]].value)))
          case predicate: SCParsedEqual =>
            val label = predicate match {
              case _: SCParsedEqual => equality
            }
            Left(PredicateFormula(label, args.map(resolveParsedTermOrFormulaInternal(_, Some(TypeTerm)).asInstanceOf[Right[Formula, Term]].value)))
        }
      case SCParsedNot(termOrFormula) =>
        typeHint.foreach { expected =>
          if(expected != TypeFormula) {
            throwTypeError(expected, TypeFormula, tree.pos)
          }
        }
        val value = resolveParsedTermOrFormulaInternal(termOrFormula, Some(TypeFormula)).asInstanceOf[Left[Formula, Term]].value
        Left(ConnectorFormula(Neg, Seq(value)))
      case binder: SCParsedBinder =>
        if(ctx.variables.contains(binder.bound)) {
          throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
        }
        val label = binder match {
          case _: SCParsedForall => Forall
          case _: SCParsedExists => Exists
          case _: SCParsedExistsOne => ExistsOne
        }
        val inner = resolveParsedTermOrFormulaInternal(binder.termOrFormula, Some(TypeFormula))(ctx.copy(variables = ctx.variables + binder.bound)).asInstanceOf[Left[Formula, Term]].value
        Left(BinderFormula(label, VariableLabel(binder.bound), inner))
    }
  }

  private def resolveParsedTermOrFormula(tree: SCParsedTermOrFormula, hint: Option[TreeType]): Either[Formula, Term] =
    resolveParsedTermOrFormulaInternal(tree, hint)(ScopedContext(Set.empty))

  def resolveFormula(tree: SCParsedTermOrFormula): Formula = resolveParsedTermOrFormula(tree, Some(TypeFormula)).asInstanceOf[Left[Formula, Term]].value

}
