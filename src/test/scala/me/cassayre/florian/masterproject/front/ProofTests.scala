package me.cassayre.florian.masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*
import lisa.kernel.proof.SCProofChecker
import lisa.kernel.Printer

class ProofTests extends AnyFunSuite {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
  val (x, y) = (VariableLabel("x"), VariableLabel("y"))

  private def checkProofs(proofs: Proof*): Unit = {
    val emptyEnvironment: ProofEnvironment = newEmptyEnvironment()
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
        RuleEliminationLeftRefl(RuleBackwardParametersBuilder.withFunction(Notations.s, t)),
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

  test("elimination rules") {
    checkProofs(
      Proof(
        (s === t) |- (t === s)
      )(
        RuleEliminationLeftSubstIff(
          RuleBackwardParametersBuilder
            .withConnector(Notations.f, identity)
            .withPredicate(Notations.a, t === s)
            .withPredicate(Notations.b, s === t)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t) |- (s === t)),
        RuleHypothesis(),
      ),
      Proof(
        (s === t) |- (t === s)
      )(
        RuleEliminationRightSubstIff(
          RuleBackwardParametersBuilder
            .withConnector(Notations.f, identity)
            .withPredicate(Notations.a, s === t)
            .withPredicate(Notations.b, t === s)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t) |- (s === t)),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, t === u) |- (s === u)
      )(
        RuleEliminationLeftSubstEq(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, _ === u)
            .withFunction(Notations.s, s)
            .withFunction(Notations.t, t)
        ),
        RuleHypothesis(),
        RuleHypothesis(),
      ),
      Proof(
        (s === t, t === u) |- (s === u)
      )(
        RuleEliminationRightSubstEq(
          RuleBackwardParametersBuilder
            .withPredicate(Notations.p, _ === u)
            .withFunction(Notations.s, t)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(),
        TacticalRewrite((s === t, t === u) |- (s === t)),
        RuleHypothesis(),
      ),
    )
  }

  test("environment") {
    val ctx = newEmptyEnvironment()

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
