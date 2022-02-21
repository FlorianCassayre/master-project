package masterproject

import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import lisa.settheory.AxiomaticSetTheory._
import org.scalatest.funsuite.AnyFunSuite
import masterproject.SCProofBuilder.*

import util.chaining.*
import scala.util.{Failure, Success, Try}

class ProofStepFinderTests extends AnyFunSuite {

  test("Proof steps reconstruction") {
    // These tests ensure that all the kernel proof steps can be generated
    // To achieve that, we design proofs that require these steps to be used at some point

    val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))
    val theory = new RunningTheory()
    val (la, lb, lc) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
    Seq(la, lb, lc).foreach(theory.addSymbol)
    val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))
    val (ls, lt) = (ConstantFunctionLabel("s", 0), ConstantFunctionLabel("t", 0))
    Seq(ls, lt).foreach(theory.addSymbol)
    val (s, t) = (FunctionTerm(ls, Seq.empty), FunctionTerm(lt, Seq.empty))

    implicit class VariableLabelEq(l: VariableLabel) { // Helper due to conflicts with scalatest's `===`
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(VariableTerm(l), r))
      def ====(r: VariableLabel): Formula = PredicateFormula(equality, Seq(VariableTerm(l), VariableTerm(r)))
    }
    implicit class FunctionLabelEq(l: FunctionLabel) {
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(FunctionTerm(l, Seq.empty), r))
      def ====(r: FunctionLabel): Formula = PredicateFormula(equality, Seq(FunctionTerm(l, Seq.empty), FunctionTerm(r, Seq.empty)))
    }
    implicit class TerEq(l: Term) {
      def ====(r: Term): Formula = PredicateFormula(equality, Seq(l, r))
      def ====(r: FunctionLabel): Formula = PredicateFormula(equality, Seq(l, FunctionTerm(r, Seq.empty)))
    }

    val proofs = Seq(
      // (1.1)
      "Hypothesis" -> SCProofBuilder(
        a |- a,
      ),
      "Cut" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by (0),
        c |- c,
        c |- Seq(b, c) by (2),
        Seq(a, c) |- Seq(a, c) by (1, 3),
      ),
      "LeftAnd" -> SCProofBuilder(
        a |- a,
        (a /\ b) |- a by 0,
      ),
      "RightAnd" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, b) |- (a /\ b) by (0, 1),
      ),
      "LeftOr" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, b, a \/ b) |- Seq(a, b) by (0, 1)
      ),
      "RightOr" -> SCProofBuilder(
        a |- a,
        a |- (a \/ b) by 0,
      ),
      "LeftImplies" -> SCProofBuilder(
        a |- a,
        b |- b,
        Seq(a, a ==> b) |- b by (0, 1),
      ),
      "RightImplies" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, a ==> a) by 0,
      ),
      "LeftIff" -> SCProofBuilder(
        (a ==> b) |- (a ==> b),
        (a <=> b) |- (a ==> b) by 0,
      ),
      "RightIff" -> SCProofBuilder(
        (a ==> b) |- (a ==> b),
        (b ==> a) |- (b ==> a),
        Seq(a ==> b, b ==> a) |- (a <=> b) by (0, 1),
      ),
      "LeftNot" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, b) by 0,
        Seq(a, !b) |- a by 1,
      ),
      "RightNot" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
        a |- Seq(a, !b) by 1,
      ),
      "LEftForall" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        forall(x, x ==== z) |- (y ==== z) by 0,
      ),
      "RightForall" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        (y ==== z) |- forall(x, y ==== z) by 0,
      ),
      "LeftExists" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        exists(x, y ==== z) |- (y ==== z) by 0,
      ),
      "RightExists" -> SCProofBuilder(
        (y ==== z) |- (y ==== z),
        (y ==== z) |- exists(x, x ==== z) by 0,
      ),
      "LeftExistsOne" -> SCProofBuilder(
        exists(y, forall(x, (x ==== y) <=> a)).pipe(f => f |- f),
        existsOne(x, a) |- exists(y, forall(x, (x ==== y) <=> a)) by 0,
      ),
      "RightExistsOne" -> SCProofBuilder(
        exists(y, forall(x, (x ==== y) <=> a)).pipe(f => f |- f),
        exists(y, forall(x, (x ==== y) <=> a)) |- existsOne(x, a) by 0,
      ),
      "(Left)Weakening" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
      ),
      "(Right)Weakening" -> SCProofBuilder(
        a |- a,
        a |- Seq(a, b) by 0,
      ),
      // (1.2)
      "LeftSubstEq" -> SCProofBuilder(
        (s ==== emptySet) |- (s ==== emptySet),
        Seq(s ==== t, t ==== emptySet) |- (s ==== emptySet) by 0,
      ),
      "RightSubstEq" -> SCProofBuilder(
        (s ==== emptySet) |- (s ==== emptySet),
        Seq(s ==== emptySet, s ==== t) |- Seq(s ==== emptySet, t ==== emptySet) by 0,
      ),
      "LeftSubstIff" -> SCProofBuilder(
        a |- a,
        Seq(b, a <=> b) |- a by 0,
      ),
      "RightSubstIff" -> SCProofBuilder(
        a |- a,
        Seq(a, a <=> b) |- b by 0,
      ),
      "LeftRefl" -> SCProofBuilder(
        a |- a,
        Seq(a, b) |- a by 0,
        Seq(a, b, emptySet ==== emptySet) |- a by 1,
        Seq(a, b) |- a by 2,
      ),
      "RightRefl" -> SCProofBuilder(
        () |- (emptySet ==== emptySet),
      ),
    )

    proofs.foreach { case (testname, proofBuilder) =>
      Try(proofBuilder.build) match {
        case Success(proof) =>
          SCProofChecker.checkSCProof(proof) match {
            case (true, _, _) => // OK
              println(testname)
              println(Printer.prettySCProof(proof))
              println()
            case (false, path, message) => throw new AssertionError(s"The reconstructed proof for '$testname' is incorrect:\n${Printer.prettySCProof(proof, Some((path, message)))}")
          }
        case Failure(exception) => throw new AssertionError(s"Couldn't reconstruct the proof for $testname", exception) // Couldn't reconstruct this proof
      }
    }
  }

}
