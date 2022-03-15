package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver

trait RuleDefinitions extends ProofStateDefinitions {

  private case class SideBuilder(formulas: IndexedSeq[Formula], partial: Boolean) {
    def |-(other: SideBuilder): PartialSequent = PartialSequent(formulas, other.formulas, partial, other.partial)
  }
  private def *(formulas: Formula*): SideBuilder = SideBuilder(formulas.toIndexedSeq, true)
  private def $(formulas: Formula*): SideBuilder = SideBuilder(formulas.toIndexedSeq, false)
  // This *must* be a def (see https://github.com/lampepfl/dotty/issues/14667)
  private def ** : SideBuilder = SideBuilder(IndexedSeq.empty, true)
  private def $$ : SideBuilder = SideBuilder(IndexedSeq.empty, false)
  //private def &(hypotheses: PartialSequent*): IndexedSeq[PartialSequent] = hypotheses.toIndexedSeq
  given Conversion[PartialSequent, IndexedSeq[PartialSequent]] = IndexedSeq(_)
  val __ : IndexedSeq[PartialSequent] = IndexedSeq.empty

  import Notations.*

  case object RulePropositionalSolver extends RuleSolver(
    (bot, ctx) => {
      val proof = SimplePropositionalSolver.solveSequent(bot)
      assert(proof.imports.isEmpty)
      IndexedSeq(SCSubproof(proof))
    }
  )

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
        Cut(
          bot,
          -1,
          -2,
          ctx(a),
        ),
      )
    }
  )

  case object GeneralTacticRightIff extends GeneralTactic {
    import Notations.*

    override def apply(proofGoal: Sequent, app: TacticApplication): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      app.formulas.collect { case (IndexedSeq(), IndexedSeq(i)) if proofGoal.right.indices.contains(i) =>
        val formula = proofGoal.right(i)
        val ea = instantiatePredicateSchemas(app.predicates(c), Map(e -> (app.predicates(a), Seq.empty)))
        val eb = instantiatePredicateSchemas(app.predicates(c), Map(e -> (app.predicates(b), Seq.empty)))
        if(formula == eb) { // TODO isSame
          Some(
            IndexedSeq(
              proofGoal.copy(right = (proofGoal.right.take(i) :+ ea) ++ proofGoal.right.drop(i + 1)),
              () |- app.predicates(a) <=> app.predicates(b),
            ),
            (bot: lisa.kernel.proof.SequentCalculus.Sequent) =>
              IndexedSeq(
                RightSubstIff(
                  bot +< (app.predicates(a) <=> app.predicates(b)),
                  -1,
                  app.predicates(a),
                  app.predicates(b),
                  app.predicates(c), // f(e)
                  e,
                ),
                Cut(bot, -2, 0, app.predicates(a) <=> app.predicates(b))
              )
          )
        } else {
          None
        }
      }.flatten
    }
  }

  // TODO more rules

}
