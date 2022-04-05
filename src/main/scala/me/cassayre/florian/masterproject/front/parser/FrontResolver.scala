package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*
import me.cassayre.florian.masterproject.front.parser.FrontParsed.*
import me.cassayre.florian.masterproject.front.parser.FrontReadingException.ResolutionException

import scala.util.{Failure, Success, Try}
import scala.util.parsing.input.{Position, Positional}
import scala.collection.View

private[parser] object FrontResolver {

  // Free variables must appear in the context, otherwise they will be treated as
  // nullary function terms

  case class ScopedContext(boundVariables: Set[String], freeVariables: Set[String]) {
    def variables: Set[String] = boundVariables ++ freeVariables
  }

  private def emptyScopedContext: ScopedContext = ScopedContext(Set.empty, Set.empty)

  private def resolveFunctionTermLabel(name: ParsedName, arity: Int): FunctionLabel[?] = name match {
    case ParsedConstant(identifier) => ConstantFunctionLabel(identifier, arity)
    case ParsedSchema(identifier) => SchematicFunctionLabel(identifier, arity)
  }

  private def resolvePredicateFormulaLabel(name: ParsedName, arity: Int): PredicateLabel[?] = name match {
    case ParsedConstant(identifier) => ConstantPredicateLabel(identifier, arity)
    case ParsedSchema(identifier) => SchematicPredicateLabel(identifier, arity)
  }

  private def resolveTermContext(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Term = tree match {
    case name: ParsedName =>
      // If the name is in the context, we decide that it is a variable
      if(ctx.variables.contains(name.identifier)) {
        VariableTerm(VariableLabel(name.identifier))
      } else {
        FunctionTerm(ConstantFunctionLabel(name.identifier, 0), Seq.empty)
      }
    case ParsedApplication(name, args) =>
      FunctionTerm(resolveFunctionTermLabel(name, args.size), args.map(resolveTermContext(_)))
    case product: ParsedProduct =>
      val name = product match {
        case _: ParsedOrderedPair => "ordered_pair"
        case _: ParsedSet2 => "unordered_pair"
      }
      FunctionTerm(ConstantFunctionLabel(name, 2), Seq(product.left, product.right).map(resolveTermContext(_)))
    case ParsedSet1(subtree) =>
      FunctionTerm(ConstantFunctionLabel("singleton", 1), Seq(resolveTermContext(subtree)))
    case ParsedSet0() =>
      FunctionTerm(ConstantFunctionLabel("empty_set", 0), Seq.empty)
    case ParsedPower(subtree) =>
      FunctionTerm(ConstantFunctionLabel("power_set", 1), Seq(resolveTermContext(subtree)))
    case ParsedUnion(subtree) =>
      FunctionTerm(ConstantFunctionLabel("union", 1), Seq(resolveTermContext(subtree)))
    case _ => throw ResolutionException("Type error: expected term, got formula", tree.pos)
  }

  private def resolveFormulaContext(tree: ParsedTermOrFormula)(implicit ctx: ScopedContext): Formula = tree match {
    case name: ParsedName =>
      PredicateFormula(resolvePredicateFormulaLabel(name, 0), Seq.empty)
    case ParsedApplication(name, args) =>
      PredicateFormula(resolvePredicateFormulaLabel(name, args.size), args.map(resolveTermContext(_)))
    case operator: ParsedBinaryOperator =>
      val label: Either[PredicateLabel[?], ConnectorLabel[?]] = operator match {
        case _: ParsedEqual => Left(equality)
        case _: ParsedMembership => Left(ConstantPredicateLabel("set_membership", 2))
        case _: ParsedSubset => Left(ConstantPredicateLabel("subset_of", 2))
        case _: ParsedSameCardinality => Left(ConstantPredicateLabel("same_cardinality", 2))
        case _: ParsedAnd => Right(and)
        case _: ParsedOr => Right(or)
        case _: ParsedImplies => Right(implies)
        case _: ParsedIff => Right(iff)
      }
      val args = Seq(operator.left, operator.right)
      label match {
        case Left(label) => PredicateFormula(label, args.map(resolveTermContext(_)))
        case Right(label) => ConnectorFormula(label, args.map(resolveFormulaContext(_)))
      }
    case ParsedNot(termOrFormula) =>
      ConnectorFormula(neg, Seq(resolveFormulaContext(termOrFormula)))
    case binder: ParsedBinder =>
      binder.bound.find(ctx.variables.contains).orElse(binder.bound.diff(binder.bound.distinct).headOption) match {
        case Some(bound) => throw ResolutionException(s"Name conflict: ${binder.bound}", binder.pos)
        case None => ()
      }
      val label = binder match {
        case _: ParsedForall => forall
        case _: ParsedExists => exists
        case _: ParsedExistsOne => existsOne
      }
      binder.bound.foldRight(resolveFormulaContext(binder.termOrFormula)(ctx.copy(boundVariables = ctx.boundVariables ++ binder.bound)))(
        (bound, body) => BinderFormula(label, VariableLabel(bound), body)
      )
    case _ => throw ResolutionException("Type error: expected formula, got term", tree.pos)
  }

  def resolveFormula(tree: ParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(emptyScopedContext)

  def resolveFormula(tree: ParsedTopTermOrFormula): Formula = {
    val repeated = tree.freeVariables.diff(tree.freeVariables.distinct).distinct
    if(repeated.isEmpty) {
      resolveFormulaContext(tree.termOrFormula)(ScopedContext(Set.empty, tree.freeVariables.toSet))
    } else {
      throw ResolutionException(s"Repeated free variable declaration: ${repeated.mkString(", ")}", tree.pos)
    }
  }

  def resolveSequent(tree: ParsedSequent): Sequent =
    Sequent(tree.left.map(resolveFormula).toIndexedSeq, tree.right.map(resolveFormula).toIndexedSeq)

}
