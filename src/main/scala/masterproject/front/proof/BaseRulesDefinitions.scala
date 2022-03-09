package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.Unification.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver

trait BaseRulesDefinitions extends ProofStateDefinitions {

  object Notations {
    val (a, b, c, d, e) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"), SchematicPredicateLabel[0]("d"), SchematicPredicateLabel[0]("e"))
    val f: SchematicConnectorLabel[1] = SchematicConnectorLabel[1]("f")
  }

  sealed trait RuleSolver extends Rule {
    override final def hypotheses: IndexedSeq[PartialSequent] = IndexedSeq.empty
    override final def conclusion: PartialSequent = PartialSequent(IndexedSeq.empty, IndexedSeq.empty)
  }

  case object RulePropositionalSolver extends RuleSolver {
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] = {
      val proof = SimplePropositionalSolver.solveSequent(sequentToKernel(bot))
      assert(proof.imports.isEmpty)
      IndexedSeq(SCSubproof(proof))
    }
  }

  sealed trait RuleIntroduction extends Rule

  case object RuleIntroductionLeftAnd extends RuleIntroduction {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(PartialSequent(IndexedSeq(a, b), IndexedSeq.empty))
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq(a /\ b), IndexedSeq.empty)
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(LeftAnd(bot, -1, ctx.predicates(a), ctx.predicates(b)))
  }

  case object RuleSubstituteRightIff extends Rule {
    import Notations.*

    override def hypotheses: IndexedSeq[PartialSequent] =
      IndexedSeq(
        PartialSequent(IndexedSeq.empty, IndexedSeq(f(a))),
        PartialSequent(IndexedSeq.empty, IndexedSeq(a <=> b)),
      )
    override def conclusion: PartialSequent =
      PartialSequent(IndexedSeq.empty, IndexedSeq(f(a)))
    override def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep] =
      IndexedSeq(
        RightSubstIff(???, -1, ctx.predicates(a), ctx.predicates(b), ???, e),
        Cut(bot, 0, -2, ???) // ctx.predicates(a) <=> ctx.predicates(b)
      )
  }

  // TODO more stuff

}
