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
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a /\ b) |- a()
      )(
        RuleIntroductionLeftAnd(),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a(), b()) |- (a /\ b)
      )(
        RuleIntroductionRightAnd(RuleTacticParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a \/ b) |- (a(), b())
      )(
        RuleIntroductionLeftOr(RuleTacticParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(1)),
      ),
      Proof(
        a() |- (a \/ b)
      )(
        RuleIntroductionRightOr(RuleTacticParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a ==> b, a()) |- b()
      )(
        RuleIntroductionLeftImplies(RuleTacticParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(1)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        () |- (a ==> a)
      )(
        RuleIntroductionRightImplies(RuleTacticParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
      ),
      Proof(
        (a <=> b) |- (b ==> a)
      )(
        RuleIntroductionLeftIff(RuleTacticParametersBuilder.withIndices(0)()),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a ==> b, b ==> a) |- (a <=> b)
      )(
        RuleIntroductionRightIff(RuleTacticParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(1)(0)),
      ),
      Proof(
        (a(), !a) |- b()
      )(
        RuleIntroductionLeftNot(RuleTacticParametersBuilder.withIndices(1)()),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(1)), // FIXME shouldn't it be 0?
      ),
      Proof(
        () |- (!a, a())
      )(
        RuleIntroductionRightNot(RuleTacticParametersBuilder.withIndices()(0)),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
      ),
    )
  }

  test("substitution rules") {
    checkProofs(
      Proof(
        forall(x, x === x) |- (s === s)
      )(
        RuleSubstituteLeftForall(
          RuleTacticParametersBuilder
            .withIndices(0)()
            .withPredicate(Notations.p, y === y, y)
            .withFunction(Notations.t, s)
        ),
        RuleHypothesis(RuleTacticParametersBuilder.withIndices(0)(0)),
      ),
    )
  }

}
