package masterproject.parser

import lisa.kernel.Printer
import masterproject.parser.SCParsed.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.{SCProofStep, Sequent}
import masterproject.SCProofStepFinder
import masterproject.SCProofStepFinder.NoProofStepFound
import masterproject.parser.ReadingException.ResolutionException

import scala.util.{Failure, Success, Try}
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

  def resolveProof(tree: ParsedProof): SCProof = {
    val premisesArity = Map(
      "Rewrite" -> 1,
      "Hypo." -> 0,
      "Cut" -> 2,
      "Left ∧" -> 1,
      "Left ¬" -> 1,
      "Right ∨" -> 1,
      "Right ¬" -> 1,
      "Left ∃" -> 1,
      "Left ∀" -> 1,
      "Left ∨" -> -1,
      "Right ∃" -> 1,
      "Right ∀" -> 1,
      "Right ∧" -> -1,
      "Right ↔" -> 2,
      "Right →" -> 1,
      "Weakening" -> 1,
      "Left →" -> 2,
      "Left ↔" -> 1,
      "L. Refl" -> 1,
      "R. Refl" -> 0,
      "L. SubstEq" -> 1,
      "R. SubstEq" -> 1,
      "L. SubstIff" -> 1,
      "R. SubstIff" -> 1,
      "?Fun Instantiation" -> 1,
      "?Pred Instantiation" -> 1,
      "SCSubproof (hidden)" -> 0, // FIXME?
      "Subproof" -> -1,
      "Import" -> 1,
    )

    def resolveProofLevel(tree: ParsedProof): SCProof = {
      val (steps, imports, _) = tree.steps.foldLeft((IndexedSeq.empty[SCProofStep], IndexedSeq.empty[Sequent], None: Option[Int])) { case ((currentSteps, currentImports, previousLine), step) =>
        previousLine match {
          case Some(previousIndex) =>
            val expectedIndex = previousIndex + 1
            if(step.line != expectedIndex) {
              throw ResolutionException(s"Expected line $expectedIndex, but got ${step.line} instead", step.pos)
            }
          case None =>
            if(step.line > 0) {
              throw ResolutionException(s"The index of the first proof step cannot be strictly positive", step.pos)
            }
        }

        val expectedArity = premisesArity(step.ruleName)
        val actualArity = step.premises.size
        if(expectedArity != -1 && expectedArity != actualArity) {
          throw ResolutionException(s"Rule ${step.ruleName} expects $expectedArity premises, but got $actualArity instead", step.pos)
        }

        val isImport = step.ruleName == "Import"

        if(step.line < 0) {
          if(!isImport) {
            throw ResolutionException("Negative step indices must necessarily be import statements", step.pos)
          }
        } else {
          if(isImport) {
            throw ResolutionException("Import statements can only appear on negative indices steps", step.pos)
          }
        }

        if(isImport && step.premises != Seq(0)) {
          throw ResolutionException(s"Import statements must have exactly one premise, and it should be equal to zero", step.pos)
        }

        if(!isImport) {
          step.premises.foreach { premise =>
            if((premise < 0 && -premise > currentImports.size) || (premise >= 0 && premise >= currentSteps.size)) {
              throw ResolutionException(s"Premise $premise is out of bounds", step.pos)
            }
          }
        }

        val sequent = resolveSequent(step.conclusion)

        val newLine = Some(step.line)

        if(isImport) {
          (currentSteps, sequent +: currentImports, newLine)
        } else {
          val currentProof = SCProof(currentSteps, currentImports)
          val newProof = Try(SCProofStepFinder.proofStepFinder(currentProof, sequent, step.premises)) match {
            case Success(value) if value.steps.size == currentSteps.size + 1 => value
            case Success(_) => throw ResolutionException("Limitation of SCProofStepFinder", step.pos) // TODO
            case Failure(exception: NoProofStepFound) => throw ResolutionException(exception.getMessage, step.pos)
            case Failure(e) => throw new Exception(e)
          }

          val newStep = newProof.steps.last

          (currentSteps :+ newStep, currentImports, newLine)
        }
      }

      SCProof(steps, imports)
    }

    // TODO for now we ignore subproofs (because they rely on indentation to eliminate ambiguity)
    resolveProofLevel(tree)
  }


  def resolveFormula(tree: ParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(ScopedContext(variables = Set.empty))

  def resolveSequent(tree: ParsedSequent): Sequent =
    Sequent(tree.left.map(resolveFormula).toSet, tree.right.map(resolveFormula).toSet)

}
