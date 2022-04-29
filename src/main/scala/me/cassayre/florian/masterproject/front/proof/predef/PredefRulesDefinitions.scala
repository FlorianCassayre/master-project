package me.cassayre.florian.masterproject.front.proof.predef

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import me.cassayre.florian.masterproject.front.proof.state.RuleDefinitions

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

  case object RuleHypothesis extends RuleBase(
    __,
    *(a) |- *(a),
    (bot, ctx) => IndexedSeq(Hypothesis(bot, ctx(a)))
  )

  // Introduction

  case object RuleIntroductionLeftAnd extends RuleBase(
    *(a, b) |- **,
    *(a /\ b) |- **,
    (bot, ctx) => IndexedSeq(LeftAnd(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightAnd extends RuleBase(
    (** |- *(a)) :+ (** |- *(b)),
    ** |- *(a /\ b),
    (bot, ctx) => IndexedSeq(RightAnd(bot, Seq(-1, -2), Seq(ctx(a), ctx(b))))
  )

  case object RuleIntroductionLeftOr extends RuleBase(
    (*(a) |- **) :+ (*(b) |- **),
    *(a \/ b) |- **,
    (bot, ctx) => IndexedSeq(LeftOr(bot, Seq(-1, -2), Seq(ctx(a), ctx(b))))
  )

  case object RuleIntroductionRightOr extends RuleBase(
    ** |- *(a, b),
    ** |- *(a \/ b),
    (bot, ctx) => IndexedSeq(RightOr(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftImplies extends RuleBase(
    (** |- *(a)) :+ (*(b) |- **),
    *(a ==> b) |- **,
    (bot, ctx) => IndexedSeq(LeftImplies(bot, -1, -2, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightImplies extends RuleBase(
    *(a) |- *(b),
    ** |- *(a ==> b),
    (bot, ctx) => IndexedSeq(RightImplies(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftIff extends RuleBase(
    *(a ==> b, b ==> a) |- **,
    *(a <=> b) |- **,
    (bot, ctx) => IndexedSeq(LeftIff(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightIff extends RuleBase(
    (** |- *(a ==> b)) :+ (** |- *(b ==> a)),
    ** |- *(a <=> b),
    (bot, ctx) => IndexedSeq(RightIff(bot, -1, -2, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftNot extends RuleBase(
    ** |- *(a),
    *(!a) |- **,
    (bot, ctx) => IndexedSeq(LeftNot(bot, -1, ctx(a)))
  )

  case object RuleIntroductionRightNot extends RuleBase(
    *(a) |- **,
    ** |- *(!a),
    (bot, ctx) => IndexedSeq(RightNot(bot, -1, ctx(a)))
  )

  case object RuleIntroductionRightRefl extends RuleBase(
    __,
    ** |- *(s === s),
    (bot, ctx) => IndexedSeq(RightRefl(bot, ctx(s) === ctx(s)))
  )

  // Substitution

  case object RuleIntroductionLeftForall extends RuleBase(
    *(p(t)) |- **,
    *(forall(x, p(x))) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val px = lambda.unsafe(Seq(ctx(x)))
      IndexedSeq(
        LeftForall(bot, -1, px, ctx(x), ctx(t))
      )
    }
  )

  case object RuleIntroductionRightForall extends RuleBase(
    ** |- *(p(x)),
    ** |- *(forall(x, p(x))),
    { case (bot, ctx) if !(bot.left ++ bot.right).flatMap(_.freeVariables).contains(ctx(x)) =>
      // TODO x not already free in sequent; ideally this should be handled automatically in `Rule`, not here
      val lambda = ctx.applyMultiary(p)
      val px = lambda.unsafe(Seq(ctx(x)))
      IndexedSeq(
        RightForall(bot, -1, px, x)
      )
    }
  )

  case object RuleIntroductionLeftExists extends RuleBase(
    *(p(x)) |- **,
    *(exists(x, p(x))) |- **,
    { case (bot, ctx) if !(bot.left ++ bot.right).flatMap(_.freeVariables).contains(ctx(x)) =>
      val lambda = ctx.applyMultiary(p)
      val px = lambda.unsafe(Seq(ctx(x)))
      IndexedSeq(
        LeftExists(bot, -1, px, x)
      )
    }
  )

  case object RuleIntroductionRightExists extends RuleBase(
    ** |- *(p(t)),
    ** |- *(exists(x, p(x))),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val px = lambda.unsafe(Seq(ctx(x)))
      IndexedSeq(
        RightExists(bot, -1, px, ctx(x), ctx(t))
      )
    }
  )

  case object RuleIntroductionLeftExistsOne extends RuleBase(
    *(exists(y, exists(x, (x === y) <=> p(x)))) |- **,
    *(existsOne(x, p(x))) |- **,
    (bot, ctx) => {
      // TODO y not free in p
      val lambda = ctx.applyMultiary(p)
      val px = lambda.unsafe(Seq(ctx(x)))
      ???
    }
  )

  // RuleIntroductionLeftExistsOne

  case object RuleIntroductionLeftSubstEq extends RuleBase(
    *(p(s)) |- **,
    *(s === t, p(t)) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(lambda.body).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = lambda.unsafe(Seq(label()))
      IndexedSeq(
        LeftSubstEq(bot, -1, ctx(s), ctx(t), ps, label)
      )
    }
  )

  case object RuleIntroductionRightSubstEq extends RuleBase(
    ** |- *(p(s)),
    *(s === t) |- *(p(t)),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(lambda.body).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = lambda.unsafe(Seq(label()))
      IndexedSeq(
        RightSubstEq(bot, -1, ctx(s), ctx(t), ps, label)
      )
    }
  )

  case object RuleIntroductionLeftSubstIff extends RuleBase(
    *(f(a)) |- **,
    *(a <=> b, f(b)) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        LeftSubstIff(bot, -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head)
      )
    }
  )

  case object RuleIntroductionRightSubstIff extends RuleBase(
    ** |- *(f(a)),
    *(a <=> b) |- *(f(b)),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        RightSubstIff(bot, -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head)
      )
    }
  )

  //

  case object RuleSubstituteRightIff extends RuleBase(
    (** |- *(f(a))) :+ ($$ |- $(a <=> b)),
    ** |- *(f(b)),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        RightSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  case object RuleSubstituteLeftIff extends RuleBase(
    (*(f(a)) |- **) :+ ($$ |- $(a <=> b)),
    *(f(b)) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        LeftSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  // Elimination

  case object RuleCut extends RuleBase(
    (** |- *(a)) :+ (*(a) |- **),
    ** |- **,
    (bot, ctx) => IndexedSeq(Cut(bot, -1, -2, ctx(a)))
  )

  case object RuleEliminationLeftRefl extends RuleBase(
    *(s === s) |- **,
    ** |- **,
    (bot, ctx) => IndexedSeq(LeftRefl(bot, -1, ctx(s) === ctx(s)))
  )

  case object RuleEliminationLeftAnd extends RuleBase(
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

  case object RuleEliminationRightOr extends RuleBase(
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

  case object RuleEliminationRightForallSchema extends RuleBase(
    ** |- *(forall(x, p(x))),
    ** |- *(p(t)),
    (bot, ctx) => {
      ctx(t) match {
        case FunctionTerm(_: SchematicFunctionLabel[?], Seq()) =>
          val vx = VariableTerm(ctx(x))
          val tv = ctx(t)
          val (px, pt) = (ctx(p)(vx), ctx(p)(tv))
          val fpx = forall(ctx(x), px)
          val cBot = bot -> pt
          IndexedSeq(
            Hypothesis(bot +< pt, pt),
            LeftForall(bot +< fpx, 0, px, vx.label, tv),
            Cut(bot, -1, 1, fpx),
          )
        case e => throw new MatchError(e)
      }
    }
  )

  case object RuleModusPonens extends RuleBase(
    (** |- *(a)) :+ ($(a) |- $(b)),
    ** |- *(b),
    (bot, ctx) => {
      IndexedSeq(
        Cut(bot, -1, -2, ctx(a)),
      )
    }
  )

  case object RuleIntroductionRightForallSchema extends RuleBase(
    ** |- *(p(t)),
    ** |- *(forall(x, p(x))),
    (bot, ctx) => {
      ctx(t) match {
        case FunctionTerm(pl: SchematicFunctionLabel[?], Seq()) =>
          val vx = VariableTerm(ctx(x))
          val (px, pt) = (ctx(p)(vx), ctx(p)(ctx(t)))
          val cBot = bot -> forall(ctx(x), px)
          IndexedSeq(
            Hypothesis(cBot +< px +> px, px),
            InstFunSchema(cBot +< pt +> px, 0, pl, vx, Seq.empty),
            RightForall(bot +< pt, 1, px, vx.label),
            Cut(bot, -1, 2, pt),
          )
        case e => throw new MatchError(e)
      }
    }
  )

  case object RuleEliminationLeftSubstEq extends RuleBase(
    (*(p(s)) |- **) +: (** |- *(s === t)),
    *(p(t)) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(lambda.body).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = lambda.unsafe(Seq(label()))
      IndexedSeq(
        LeftSubstEq(bot +< (ctx(s) === ctx(t)), -1, ctx(s), ctx(t), ps, label),
        Cut(bot, -2, 0, ctx(s) === ctx(t))
      )
    }
  )

  case object RuleEliminationRightSubstEq extends RuleBase(
    (** |- *(p(s))) +: (** |- *(s === t)),
    ** |- *(p(t)),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(lambda.body).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = lambda.unsafe(Seq(label()))
      IndexedSeq(
        RightSubstEq(bot +< (ctx(s) === ctx(t)), -1, ctx(s), ctx(t), ps, label),
        Cut(bot, -2, 0, ctx(s) === ctx(t))
      )
    }
  )

  case object RuleEliminationLeftSubstIff extends RuleBase(
    (*(f(a)) |- **) +: (** |- *(a <=> b)),
    *(f(b)) |- **,
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        LeftSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  case object RuleEliminationRightSubstIff extends RuleBase(
    (** |- *(f(a))) +: (** |- *(a <=> b)),
    ** |- *(f(b)),
    (bot, ctx) => {
      val lambda = ctx.applyMultiary(f)
      IndexedSeq(
        RightSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), lambda.body, lambda.parameters.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  // TODO more rules

  // Move this
  /*case class GeneralTacticRightIff(parameters: RuleTacticParameters) extends GeneralTactic {
    import Notations.*

    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      parameters.formulas.collect { case (IndexedSeq(), IndexedSeq(i)) if proofGoal.right.indices.contains(i) =>
        val formula = proofGoal.right(i)
        val ea = instantiatePredicateSchemas(parameters.predicates(c), Map(e -> (parameters.predicates(a), Seq.empty)))
        val eb = instantiatePredicateSchemas(parameters.predicates(c), Map(e -> (parameters.predicates(b), Seq.empty)))
        if(formula == eb) { // TODO isSame
          val bot: lisa.kernel.proof.SequentCalculus.Sequent = proofGoal
          Some(
            IndexedSeq(
              proofGoal.copy(right = (proofGoal.right.take(i) :+ ea) ++ proofGoal.right.drop(i + 1)),
              () |- parameters.predicates(a) <=> parameters.predicates(b),
            ),
            () =>
              IndexedSeq(
                RightSubstIff(
                  bot +< (parameters.predicates(a) <=> parameters.predicates(b)),
                  -1,
                  parameters.predicates(a),
                  parameters.predicates(b),
                  parameters.predicates(c), // f(e)
                  e,
                ),
                Cut(bot, -2, 0, parameters.predicates(a) <=> parameters.predicates(b))
              )
          )
        } else {
          None
        }
      }.flatten
    }
  }*/

}
