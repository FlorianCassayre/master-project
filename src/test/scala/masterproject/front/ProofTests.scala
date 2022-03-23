package masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.Printer

class ProofTests extends AnyFunSuite {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))
  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))


  test("introduction rules") {
    val proofs: Seq[Proof] = Seq(
      Proof(
        (a(), b /\ c) |- (b /\ c, b())
      )(
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq(0))))),
      ),
      Proof(
        (a /\ b) |- a()
      )(
        RuleIntroductionLeftAnd(),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
      ),
      Proof(
        (a(), b()) |- (a /\ b)
      )(
        RuleIntroductionRightAnd(RuleTacticParameters(Some((IndexedSeq.empty, IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq(0))))),
      ),
      Proof(
        (a \/ b) |- (a(), b())
      )(
        RuleIntroductionLeftOr(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq.empty)))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(1))))),
      ),
      Proof(
        a() |- (a \/ b)
      )(
        RuleIntroductionRightOr(RuleTacticParameters(Some((IndexedSeq.empty, IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
      ),
      Proof(
        (a ==> b, a()) |- b()
      )(
        RuleIntroductionLeftImplies(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq.empty)))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(1))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq(0))))),
      ),
      Proof(
        () |- (a ==> a)
      )(
        RuleIntroductionRightImplies(RuleTacticParameters(Some((IndexedSeq.empty, IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
      ),
      Proof(
        (a <=> b) |- (b ==> a)
      )(
        RuleIntroductionLeftIff(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq.empty)))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq(0))))),
      ),
      Proof(
        (a ==> b, b ==> a) |- (a <=> b)
      )(
        RuleIntroductionRightIff(RuleTacticParameters(Some((IndexedSeq.empty, IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq(0))))),
      ),
      Proof(
        (a(), !a) |- b()
      )(
        RuleIntroductionLeftNot(RuleTacticParameters(Some((IndexedSeq(1), IndexedSeq.empty)))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(1))))), // FIXME shouldn't it be 0?
      ),
      Proof(
        () |- (!a, a())
      )(
        RuleIntroductionRightNot(RuleTacticParameters(Some((IndexedSeq.empty, IndexedSeq(0))))),
        RuleHypothesis(RuleTacticParameters(Some((IndexedSeq(0), IndexedSeq(0))))),
      ),
    )

    val emptyEnvironment: ReadableProofEnvironment = _ => false
    proofs.foreach { proof =>
      val result = reconstructSCProof(proof, emptyEnvironment)
      assert(result.nonEmpty)
      val scProof = result.get._1
      val judgement = SCProofChecker.checkSCProof(scProof)
      println(Printer.prettySCProof(scProof, judgement))
      println()
      assert(judgement.isValid)
      assert(scProof.imports.isEmpty)
      assert(lisa.kernel.proof.SequentCalculus.isSameSequent(scProof.conclusion, proof.initialState.goals.head))
    }
  }

}
