package masterproject

import lisa.KernelHelpers.*
import lisa.kernel.Printer
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.settheory.AxiomaticSetTheory.*
import org.scalatest.funsuite.AnyFunSuite
import masterproject.SCProofBuilder.*
import masterproject.MonadicSCProofBuilder.*
import proven.tactics.ProofTactics.*

import util.chaining.*
import scala.util.{Failure, Success, Try}

class MonadicSCProofBuilderTests extends AnyFunSuite {
  private def variable(name: String): VariableTerm = VariableTerm(VariableLabel(name))
  private val (x, y, z, w, xp, yp, zp, wp) = (variable("x"), variable("y"), variable("z"), variable("w"), variable("x'"), variable("y'"), variable("z'"), variable("w'"))

  test("monadic proof builder") {

    // We adapted a proof from `ElementsOfSetTheoryTests` to compare the syntax
    // Note that subproofs are currently not supported in this format

    val proof: SCProof = MonadicSCProofBuilder.create(for {
      (t0, _) <- () |- pairAxiom justifiedBy (() |- pairAxiom)
      (t1, _) <- (p: SCProof) => instantiateForall(p, t0.right.head, y) // (*)
      (t2, _) <- (p: SCProof) => instantiateForall(p, t1.right.head, y)
      (_, i0) <- (p: SCProof) => instantiateForall(p, t2.right.head, x)
      f = y === x
      (_, h0) <- f |- f                             // Hypo.
      (_, h1) <- f |- (f \/ f) by h0                // Right ∨ 0
      (_, h2) <- (f \/ f) |- f by h0                // Left  ∨ 0,0
      (_, h3) <- () |- (f ==> (f \/ f)) by h1       // Right → 1
      (_, h4) <- () |- ((f \/ f) ==> f) by h2       // Right → 2
      (_, i1) <- () |- (f <=> (f \/ f)) by (h3, h4) // Right ↔ 3,4
      xy = y === x
      (_, i2) <- ((xy \/ xy) <=> xy) |- (xy <=> in(x, pair(y, y))) by (i0, i1)
      _ <- () |- (xy <=> in(x, pair(y, y))) by i2
      _ <- (p: SCProof) => generalizeToForall(p, y.label)
      _ <- (p: SCProof) => generalizeToForall(p, x.label)
    } yield ())

    // (*): Eventually this could be replaced by another method which takes only the last argument (the first two will be inferred)

    val result = SCProofChecker.checkSCProof(proof)
    assert(result._1, (result._2, result._3))

    assert(isSameSequent(() |- forall(x.label, forall(y.label, (x === y) <=> in(x, pair(y, y)))), proof.conclusion),
      s"Unexpected conclusion: ${Printer.prettySequent(proof.conclusion)} (expected: ${Printer.prettySequent(proof.conclusion)})")
  }
}
