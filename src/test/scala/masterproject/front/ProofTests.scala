package masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.Printer

class ProofTests extends AnyFunSuite {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))
  val (s, t) = (ConstantFunctionLabel[0]("s"), ConstantFunctionLabel[0]("t"))
  val (x, y) = (VariableLabel("x"), VariableLabel("y"))

  private def checkProofs(proofs: Proof*): Unit = {
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

  test("introduction rules") {
    checkProofs(
      Proof(
        (a(), b /\ c) |- (b /\ c, b())
      )(
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a /\ b) |- a()
      )(
        RuleIntroductionLeftAnd(),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a(), b()) |- (a /\ b)
      )(
        RuleIntroductionRightAnd(RuleBackwardParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a \/ b) |- (a(), b())
      )(
        RuleIntroductionLeftOr(RuleBackwardParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(1)),
      ),
      Proof(
        a() |- (a \/ b)
      )(
        RuleIntroductionRightOr(RuleBackwardParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a ==> b, a()) |- b()
      )(
        RuleIntroductionLeftImplies(RuleBackwardParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(1)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        () |- (a ==> a)
      )(
        RuleIntroductionRightImplies(RuleBackwardParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a <=> b) |- (b ==> a)
      )(
        RuleIntroductionLeftIff(RuleBackwardParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a ==> b, b ==> a) |- (a <=> b)
      )(
        RuleIntroductionRightIff(RuleBackwardParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a(), !a) |- b()
      )(
        RuleIntroductionLeftNot(RuleBackwardParametersBuilder.withIndices(1)()),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(1)), // FIXME shouldn't it be 0?
      ),
      Proof(
        () |- (!a, a())
      )(
        RuleIntroductionRightNot(RuleBackwardParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
      ),
    )
  }

  test("substitution rules") {
    checkProofs(
      Proof(
        forall(x, x === x) |- (s === s)
      )(
        RuleSubstituteLeftForall(
          RuleBackwardParametersBuilder
            .withIndices(0)()
            .withPredicate(Notations.p, x => x === x)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(RuleBackwardParametersBuilder.withIndices(0)(0)),
      ),
    )

    // TODO all the remaining rules
  }

  test("environment") {
    val ctx = new ProofEnvironment

    val thm1 = ctx.mkTheorem(
      Proof(
        () |- ((a /\ b) ==> (b /\ a))
      )(
        GeneralTacticSolver,
      )
    )

    val thm2 = ctx.mkTheorem(
      Proof(
        () |- ((b /\ a) ==> (a /\ b))
      )(
        GeneralTacticSolver,
      )
    )

    val thm3 = RuleIntroductionRightIff(thm1, thm2).get

    val reconstructed = reconstructSCProofForTheorem(thm3)

    println(Printer.prettySCProof(reconstructed))

    assert(SCProofChecker.checkSCProof(reconstructed).isValid)
  }

}
