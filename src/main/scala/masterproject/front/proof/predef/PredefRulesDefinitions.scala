package masterproject.front.proof.predef

import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import masterproject.front.proof.state.RuleDefinitions

trait PredefRulesDefinitions extends RuleDefinitions {

  private case class SideBuilder(formulas: IndexedSeq[Formula], partial: Boolean) {
    def |-(other: SideBuilder): PartialSequent = PartialSequent(formulas, other.formulas, partial, other.partial)
  }
  private def *(formulas: Formula*): SideBuilder = SideBuilder(formulas.toIndexedSeq, true)
  private def $(formulas: Formula*): SideBuilder = SideBuilder(formulas.toIndexedSeq, false)
  // This *must* be a def (see https://github.com/lampepfl/dotty/issues/14667)
  private def ** : SideBuilder = SideBuilder(IndexedSeq.empty, true)
  private def $$ : SideBuilder = SideBuilder(IndexedSeq.empty, false)
  //private def &(hypotheses: PartialSequent*): IndexedSeq[PartialSequent] = hypotheses.toIndexedSeq
  private given Conversion[PartialSequent, IndexedSeq[PartialSequent]] = IndexedSeq(_)
  private val __ : IndexedSeq[PartialSequent] = IndexedSeq.empty

  import Notations.*

  case object RuleHypothesis extends RuleIntroduction(
    __,
    *(a) |- *(a),
    (bot, ctx) => IndexedSeq(Hypothesis(bot, ctx(a)))
  )

  case object RuleIntroductionLeftAnd extends RuleIntroduction(
    *(a, b) |- **,
    *(a /\ b) |- **,
    (bot, ctx) => IndexedSeq(LeftAnd(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightAnd extends RuleIntroduction(
    (** |- *(a)) :+ (** |- *(b)),
    ** |- *(a, b),
    (bot, ctx) => IndexedSeq(RightAnd(bot, Seq(-1, -2), Seq(ctx(a), ctx(b))))
  )

  case object RuleEliminationLeftAnd extends RuleElimination(
    *(a /\ b) |- **,
    *(a, b) |- **,
    (bot, ctx) =>
      IndexedSeq(
        Hypothesis(bot +> ctx(a), ctx(a)),
        Hypothesis(bot +> ctx(b), ctx(b)),
        RightAnd(bot +> (ctx(a) /\ ctx(b)), Seq(0, 1), Seq(ctx(a), ctx(b))),
        Cut(bot, 2, -1, ctx(a) /\ ctx(b)),
      )
  )

  case object RuleEliminationRightOr extends RuleElimination(
    ** |- *(a \/ b),
    ** |- *(a, b),
    (bot, ctx) =>
      IndexedSeq(
        Hypothesis(bot +< ctx(a), ctx(a)),
        Hypothesis(bot +< ctx(b), ctx(b)),
        LeftOr(bot +< (ctx(a) \/ ctx(b)), Seq(0, 1), Seq(ctx(a), ctx(b))),
        Cut(bot, -1, 2, ctx(a) \/ ctx(b)),
      )
  )

  case object RuleSubstituteRightIff extends RuleSubstitution(
    (** |- *(f(a))) :+ ($$ |- $(a <=> b)),
    ** |- *(f(b)),
    (bot, ctx) => {
      val (fBody, fArgs) = ctx(f)
      IndexedSeq(
        RightSubstIff(
          bot +< (ctx(a) <=> ctx(b)),
          -1,
          ctx(a),
          ctx(b),
          fBody,
          fArgs.head,
        ),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  case object RuleSubstituteLeftIff extends RuleSubstitution(
    (*(f(a)) |- **) :+ ($$ |- $(a <=> b)),
    *(f(b)) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx(f)
      IndexedSeq(
        LeftSubstIff(
          bot +< (ctx(a) <=> ctx(b)),
          -1,
          ctx(a),
          ctx(b),
          fBody,
          fArgs.head,
        ),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  case object RuleModusPonens extends RuleElimination(
    (** |- *(a)) :+ ($(a) |- $(b)),
    ** |- *(b),
    (bot, ctx) => {
      IndexedSeq(
        Cut(bot, -1, -2, ctx(a)),
      )
    }
  )

  // TODO more rules

}
