package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver

trait BaseRulesDefinitions extends ProofStateDefinitions {

  case object RulePropositionalSolver extends RuleSolver {
    override def reconstruct(bot: lisa.kernel.proof.SequentCalculus.Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] = {
      val proof = SimplePropositionalSolver.solveSequent(bot)
      assert(proof.imports.isEmpty)
      IndexedSeq(SCSubproof(proof))
    }
  }

  case object RuleIntroductionLeftAnd extends RuleIntroduction {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(PartialSequent(IndexedSeq(a, b), IndexedSeq.empty))
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq(a /\ b), IndexedSeq.empty)
    override def reconstruct(bot: lisa.kernel.proof.SequentCalculus.Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(LeftAnd(bot, -1, ctx.predicates(a), ctx.predicates(b)))
  }

  case object RuleIntroductionRightAnd extends RuleIntroduction {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(
        PartialSequent(IndexedSeq.empty, IndexedSeq(a)),
        PartialSequent(IndexedSeq.empty, IndexedSeq(b)),
      )
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq.empty, IndexedSeq(a /\ b))
    override def reconstruct(bot: lisa.kernel.proof.SequentCalculus.Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(RightAnd(bot, Seq(-1, -2), Seq(ctx.predicates(a), ctx.predicates(b))))
  }

  case object RuleEliminationLeftAnd extends RuleElimination {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(PartialSequent(IndexedSeq(a /\ b), IndexedSeq.empty))
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq(a, b), IndexedSeq.empty)
    override def reconstruct(bot: lisa.kernel.proof.SequentCalculus.Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(
        Hypothesis(bot +> ctx.predicates(a), ctx.predicates(a)),
        Hypothesis(bot +> ctx.predicates(b), ctx.predicates(b)),
        RightAnd(bot +> (ctx.predicates(a) /\ ctx.predicates(b)), Seq(0, 1), Seq(ctx.predicates(a), ctx.predicates(b))),
        Cut(bot, 2, -1, ctx.predicates(a) /\ ctx.predicates(b)),
      )
  }

  case object RuleSubstituteRightIff extends StaticRule {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(
        PartialSequent(IndexedSeq.empty, IndexedSeq(f(a))),
        PartialSequent(IndexedSeq.empty, IndexedSeq(a <=> b)),
      )
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq.empty, IndexedSeq(f(a)))
    override def reconstruct(bot: lisa.kernel.proof.SequentCalculus.Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(
        RightSubstIff(???, -1, ctx.predicates(a), ctx.predicates(b), ???, e),
        Cut(bot, 0, -2, ???) // ctx.predicates(a) <=> ctx.predicates(b)
      )
  }

  // TODO more stuff

}
