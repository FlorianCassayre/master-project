package me.cassayre.florian.masterproject.util

import scala.language.adhocExtensions

import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.*
import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.util.SCProofBuilder.*
import me.cassayre.florian.masterproject.util.MonadicSCProofBuilder.*
import proven.tactics.ProofTactics.*

import util.chaining.*
import scala.util.{Failure, Success, Try}

class MonadicSCProofBuilderTests extends AnyFunSuite {
  private def variable(name: String): VariableTerm = VariableTerm(VariableLabel(name))
  private val (x, y, z, w, xp, yp, zp, wp) = (variable("x"), variable("y"), variable("z"), variable("w"), variable("x'"), variable("y'"), variable("z'"), variable("w'"))

  // Shorthands
  private def withForallInstantiation(ts: Term*): SCProof => SCProof = p => instantiateForall(p, ts*)
  private def withForallGeneralization(xs: VariableTerm*): SCProof => SCProof = p => generalizeToForall(p, xs.map(_.label)*)

  test("monadic proof builder") {

    // We adapted a proof from `ElementsOfSetTheoryTests` to compare the syntax

    val proof: SCProof = MonadicSCProofBuilder.create(for {
      (_, i0) <- MonadicSCProofBuilder.subproof(for {
        _ <- (() |- pairAxiom).justified
        _ <- withForallInstantiation(y)
        _ <- withForallInstantiation(y)
        _ <- withForallInstantiation(x)
      } yield ())
      f = y === x
      (_, i1) <- MonadicSCProofBuilder.subproof(for {
        (_, h0) <- f |- f                       // Hypo.
        (_, h1) <- f |- (f \/ f) by h0          // Right ∨ 0
        (_, h2) <- (f \/ f) |- f by h0          // Left  ∨ 0,0
        (_, h3) <- () |- (f ==> (f \/ f)) by h1 // Right → 1
        (_, h4) <- () |- ((f \/ f) ==> f) by h2 // Right → 2
        _ <- () |- (f <=> (f \/ f)) by (h3, h4) // Right ↔ 3,4
      } yield ())
      xy = y === x
      (_, i2) <- ((xy \/ xy) <=> xy) |- (xy <=> in(x, pair(y, y))) by (i0, i1)
      _ <- () |- (xy <=> in(x, pair(y, y))) by i2
      _ <- withForallGeneralization(y)
      _ <- withForallGeneralization(x)
    } yield ())

    val judgement = SCProofChecker.checkSCProof(proof)
    assert(judgement.isValid, judgement)

    assert(isSameSequent(() |- forall(x.label, forall(y.label, (x === y) <=> in(x, pair(y, y)))), proof.conclusion),
      s"Unexpected conclusion: ${Printer.prettySequent(proof.conclusion)} (expected: ${Printer.prettySequent(proof.conclusion)})")
  }

  test("proof builder on a larger proof") {
    // proofUnorderedPairDeconstruction
    val (x1, y1) = (variable("x1"), variable("y1"))
    val pxy = pair(x, y)
    val pxy1 = pair(x1, y1)
    val g = SchematicFunctionLabel("g", 0)
    val zf = in(z, pxy)
    val proof: SCProof = MonadicSCProofBuilder.create(for {
      (_, i0) <- MonadicSCProofBuilder.subproof(for {
        (_, h0) <- zf |- zf
        (_, h1) <- () |- (zf ==> zf) by h0
        (_, h2) <- () |- (zf <=> zf) by h1
        _ <- RightSubstEq((pxy === pxy1) |- (zf <=> in(z, pxy1)), h2, List(pxy -> pxy1), LambdaTermFormula(Seq(g), zf <=> in(z, FunctionTerm(g, Seq.empty))))
      } yield (), display = false)
      (_, i1) <- MonadicSCProofBuilder.subproof(for {
        _ <- (() |- pairAxiom).justified
        _ <- withForallInstantiation(x, y, z)
      } yield (), display = false)
      (p2, i2) <- MonadicSCProofBuilder.subproof(for {
        _ <- (() |- pairAxiom).justified
        _ <- withForallInstantiation(x1, y1, z)
      } yield (), display = false)
      (p3, i3) <- RightSubstEq(
        (pxy === pxy1) |- (in(z, pxy1) <=> ((z === x) \/ (z === y))), i1, List(pxy -> pxy1), LambdaTermFormula(Seq(g), in(z, FunctionTerm(g, Seq.empty)) <=> ((z === x) \/ (z === y)))
      )
      (_, i4) <- (pxy === pxy1) |- (in(z, pxy1) <=> ((z === x) \/ (z === y))) by i3
    } yield ())

    val judgement = SCProofChecker.checkSCProof(proof)
    assert(judgement.isValid, judgement)
  }
}
