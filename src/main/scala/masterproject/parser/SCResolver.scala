package masterproject.parser

import lisa.kernel.Printer
import masterproject.parser.SCParsed.*
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
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
    val stepsMetadata: Map[String, (Int, Class[_])] = Map(
      "Rewrite" -> (1, classOf[Rewrite]),
      "Hypo." -> (0, classOf[Hypothesis]),
      "Cut" -> (2, classOf[Cut]),
      "Left ∧" -> (1, classOf[LeftAnd]),
      "Left ¬" -> (1, classOf[LeftNot]),
      "Right ∨" -> (1, classOf[RightOr]),
      "Right ¬" -> (1, classOf[RightNot]),
      "Left ∃" -> (1, classOf[LeftExists]),
      "Left ∀" -> (1, classOf[LeftForall]),
      "Left ∨" -> (-1, classOf[LeftOr]),
      "Right ∃" -> (1, classOf[RightExists]),
      "Right ∀" -> (1, classOf[RightForall]),
      "Right ∧" -> (-1, classOf[RightAnd]),
      "Right ↔" -> (2, classOf[RightIff]),
      "Right →" -> (1, classOf[RightImplies]),
      "Weakening" -> (1, classOf[Weakening]),
      "Left →" -> (2, classOf[LeftImplies]),
      "Left ↔" -> (1, classOf[LeftIff]),
      "L. Refl" -> (1, classOf[LeftRefl]),
      "R. Refl" -> (0, classOf[RightRefl]),
      "L. SubstEq" -> (1, classOf[LeftSubstEq]),
      "R. SubstEq" -> (1, classOf[RightSubstEq]),
      "L. SubstIff" -> (1, classOf[LeftSubstIff]),
      "R. SubstIff" -> (1, classOf[RightSubstIff]),
      "?Fun Instantiation" -> (1, classOf[InstFunSchema]),
      "?Pred Instantiation" -> (1, classOf[InstPredSchema]),
      "SCSubproof (hidden)" -> (0, classOf[SCSubproof]), // FIXME (name)
      "Subproof" -> (-1, classOf[SCSubproof]),
      "Import" -> (1, null),
    )

    case class StackEntry(steps: IndexedSeq[SCProofStep], imports: IndexedSeq[Sequent], subproofPremises: Seq[Int], nextLineNumber: Int, indentation: Int)

    def foldSubproofs(stack: Seq[StackEntry], position: Position): Option[SCSubproof] = {
      stack.foldLeft(None: Option[SCSubproof]) { (subproofOpt, entry) =>
        val premises = entry.subproofPremises
        val newSteps = subproofOpt match {
          case Some(proof) => entry.steps :+ proof.copy(premises = premises)
          case None => entry.steps
        }
        if(newSteps.isEmpty) {
          throw ResolutionException("This proof or subproof is incomplete", position)
        }
        Some(SCSubproof(SCProof(newSteps, entry.imports)))
      }
    }

    val (finalStack, finalExpectedDeeperIndentation) = tree.steps.foldLeft(
      (Seq.empty[StackEntry], true)
    ) { case ((stack, expectedDeeperIndentation), parsedStep) =>
      // The true indentation of the current step
      val rightIndentation = parsedStep.indentation + parsedStep.line.toString.length

      val newStack =
        if(expectedDeeperIndentation) { // Either the first line of a subproof or the first line of the proof
          stack match {
            case entry +: _ => // First step inside a subproof
              if (rightIndentation <= entry.indentation) {
                throw ResolutionException("The content of this subproof must be indented further", parsedStep.stepPosition)
              }
              val importsSize = entry.subproofPremises.size
              if(-parsedStep.line != importsSize) {
                throw ResolutionException(s"The parent subproof declared $importsSize premise(s), therefore this line must start with index ${-importsSize}", parsedStep.stepPosition)
              }
            case _ => // Very first line of the proof
              ()
          }
          if (parsedStep.line > 0) {
            throw ResolutionException(s"The index of the first proof step cannot be strictly positive", parsedStep.stepPosition)
          }
          val entry = StackEntry(IndexedSeq.empty, IndexedSeq.empty, Seq.empty, parsedStep.line, rightIndentation)
          entry +: stack
        } else { // A line at the same level or lower
          assert(stack.nonEmpty) // Invariant

          val indentationIndex = stack.zipWithIndex.find { case (entry, _) => entry.indentation == rightIndentation }.map(_._2)
          indentationIndex match {
            case Some(delta) =>
              val previousEntry: StackEntry = stack(delta)
              previousEntry.copy(steps = previousEntry.steps ++ foldSubproofs(stack.take(delta), parsedStep.stepPosition).map(sp => sp.copy(premises = previousEntry.subproofPremises)).toSeq) +: stack.drop(delta + 1)
            case None =>
              throw ResolutionException("This step is not properly indented", parsedStep.stepPosition)
          }
        }

      assert(newStack.nonEmpty) // Invariant

      val entry = newStack.head
      val tail = newStack.tail

      if (parsedStep.line != entry.nextLineNumber) {
        throw ResolutionException(s"Expected line to be numbered ${entry.nextLineNumber}, but got ${parsedStep.line} instead", parsedStep.stepPosition)
      }

      val (expectedArity, clazz) = stepsMetadata(parsedStep.ruleName)
      val actualArity = parsedStep.premises.size
      if(expectedArity != -1 && expectedArity != actualArity) {
        throw ResolutionException(s"Rule ${parsedStep.ruleName} expects $expectedArity premises, but got $actualArity instead", parsedStep.stepPosition)
      }

      val isImport = parsedStep.ruleName == "Import"
      val isSubproof = parsedStep.ruleName == "Subproof" // Hidden is excluded from this

      if(parsedStep.ruleName == "SCSubproof (hidden)") {
        throw ResolutionException("Cannot parse a hidden subproof", parsedStep.stepPosition)
      }

      if(parsedStep.line < 0) {
        if(!isImport) {
          throw ResolutionException("Negative step indices must necessarily be import statements", parsedStep.stepPosition)
        }
      } else {
        if(isImport) {
          throw ResolutionException("Import statements can only appear on negative indices steps", parsedStep.stepPosition)
        }
      }

      if(isImport && parsedStep.premises != Seq(0)) {
        throw ResolutionException("Import statements must have exactly one premise, and it should be equal to zero", parsedStep.stepPosition)
      }

      if(!isImport) {
        parsedStep.premises.foreach { premise =>
          if((premise < 0 && -premise > entry.imports.size) || (premise >= 0 && premise >= entry.steps.size)) {
            throw ResolutionException(s"Premise $premise is out of bounds", parsedStep.stepPosition)
          }
        }
      }

      val sequent = resolveSequent(parsedStep.conclusion)

      val newLine = Some(parsedStep.line)

      val newEntry = entry.copy(nextLineNumber = entry.nextLineNumber + 1, subproofPremises = Seq.empty)

      if(isImport) {
        (newEntry.copy(imports = sequent +: newEntry.imports) +: tail, false)
      } else if(isSubproof) {
        (newEntry.copy(subproofPremises = parsedStep.premises) +: tail, true)
      } else {
        val currentProof = SCProof(newEntry.steps, newEntry.imports)
        val newStep =
          SCProofStepFinder
            .findPossibleProofSteps(currentProof, sequent, parsedStep.premises).find(candidateStep => candidateStep.getClass.getName == clazz.getName && candidateStep.premises == parsedStep.premises) match {
            case Some(stepFound) => stepFound
            case None =>
              throw ResolutionException("Couldn't reconstruct this kernel step", parsedStep.stepPosition)
          }

        (newEntry.copy(steps = newEntry.steps :+ newStep) +: tail, isSubproof)
      }
    }

    val lastPosition = tree.steps.last.stepPosition
    if(finalExpectedDeeperIndentation) {
      throw ResolutionException("Empty trailing subproof", lastPosition)
    }

    val finalStep = foldSubproofs(finalStack, lastPosition)
    finalStep.get.sp
  }

  def resolveFormula(tree: ParsedTermOrFormula): Formula =
    resolveFormulaContext(tree)(ScopedContext(variables = Set.empty))

  def resolveSequent(tree: ParsedSequent): Sequent =
    Sequent(tree.left.map(resolveFormula).toSet, tree.right.map(resolveFormula).toSet)

}
