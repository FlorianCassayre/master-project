package masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.Printer

class ProofTests extends AnyFunSuite {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))
  val (s, t, u) = (ConstantFunctionLabel[0]("s"), ConstantFunctionLabel[0]("t"), ConstantFunctionLabel[0]("u"))
  val (x, y) = (VariableLabel("x"), VariableLabel("y"))

  private def checkProofs(proofs: Proof*): Unit = {
    val emptyEnvironment: ProofEnvironment = new ProofEnvironment {
      override def contains(sequent: Sequent): Boolean = false
    }
    proofs.foreach { proof =>
      val result = evaluateProof(proof)(emptyEnvironment).map(reconstructSCProof)
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
      Proof(
        () |- (t === t)
      )(
        RuleIntroductionLeftRefl(RuleBackwardParametersBuilder.withFunction(Notations.s, t)),
        RuleHypothesis(),
      ),
      Proof(
        () |- (t === t)
      )(
        RuleIntroductionRightRefl(RuleBackwardParametersBuilder.withFunction(Notations.s, t)),
      ),
    )
  }

  test("introduction higher order") {
    checkProofs(
      Proof(
        forall(x, u === x) |- (u === s)
      )(
        RuleIntroductionLeftForall(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, x => u === x)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(),
      ),
      Proof(
        a() |- forall(x, (u === x) \/ a)
      )(
        RuleIntroductionRightForall(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, x => (u === x) \/ a)
        ),
        RuleIntroductionRightOr(),
        RuleHypothesis(),
      ),
      Proof(
        exists(x, (s === x) /\ a) |- a()
      )(
        RuleIntroductionLeftExists(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, x => (s === x) /\ a)
        ),
        RuleIntroductionLeftAnd(),
        RuleHypothesis(),
      ),
      Proof(
        (s === t) |- exists(x, s === x)
      )(
        RuleIntroductionRightExists(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, s === _)
            .withFunction(Notations.t, t)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, u === t) |- (u === s)
      )(
        RuleIntroductionLeftSubstEq(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, u === s) |- (u === t)
      )(
        RuleIntroductionRightSubstEq(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, u === _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (a <=> b, c <=> b) |- (c <=> a)
      )(
        RuleIntroductionLeftSubstIff(
          RuleBackwardParametersBuilder
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis(),
      ),
      Proof(
        (a <=> b, c <=> a) |- (c <=> b)
      )(
        RuleIntroductionRightSubstIff(
          RuleBackwardParametersBuilder
            .withConnector(Notations.f, c <=> _)
        ),
        RuleHypothesis(),
      ),
    )

    // TODO remaining rules
  }

  test("environment") {
    val ctx = new ProofEnvironment

    val thm1 = ctx.mkTheorem(
      Proof(
        () |- ((a /\ b) ==> (b /\ a))
      )(
        TacticSolver,
      )
    )

    val thm2 = ctx.mkTheorem(
      Proof(
        () |- ((b /\ a) ==> (a /\ b))
      )(
        TacticSolver,
      )
    )

    val thm3 = RuleIntroductionRightIff(thm1, thm2).get

    val reconstructed = reconstructSCProofForTheorem(thm3)

    println(Printer.prettySCProof(reconstructed))

    assert(SCProofChecker.checkSCProof(reconstructed).isValid)
  }

}
