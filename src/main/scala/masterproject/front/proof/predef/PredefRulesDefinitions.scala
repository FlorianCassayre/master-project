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

  // Introduction

  case object RuleIntroductionLeftAnd extends RuleIntroduction(
    *(a, b) |- **,
    *(a /\ b) |- **,
    (bot, ctx) => IndexedSeq(LeftAnd(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightAnd extends RuleIntroduction(
    (** |- *(a)) :+ (** |- *(b)),
    ** |- *(a /\ b),
    (bot, ctx) => IndexedSeq(RightAnd(bot, Seq(-1, -2), Seq(ctx(a), ctx(b))))
  )

  case object RuleIntroductionLeftOr extends RuleIntroduction(
    (*(a) |- **) :+ (*(b) |- **),
    *(a \/ b) |- **,
    (bot, ctx) => IndexedSeq(LeftOr(bot, Seq(-1, -2), Seq(ctx(a), ctx(b))))
  )

  case object RuleIntroductionRightOr extends RuleIntroduction(
    ** |- *(a, b),
    ** |- *(a \/ b),
    (bot, ctx) => IndexedSeq(RightOr(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftImplies extends RuleIntroduction(
    (** |- *(a)) :+ (*(b) |- **),
    *(a ==> b) |- **,
    (bot, ctx) => IndexedSeq(LeftImplies(bot, -1, -2, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightImplies extends RuleIntroduction(
    *(a) |- *(b),
    ** |- *(a ==> b),
    (bot, ctx) => IndexedSeq(RightImplies(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftIff extends RuleIntroduction(
    *(a ==> b, b ==> a) |- **,
    *(a <=> b) |- **,
    (bot, ctx) => IndexedSeq(LeftIff(bot, -1, ctx(a), ctx(b)))
  )

  case object RuleIntroductionRightIff extends RuleIntroduction(
    (** |- *(a ==> b)) :+ (** |- *(b ==> a)),
    ** |- *(a <=> b),
    (bot, ctx) => IndexedSeq(RightIff(bot, -1, -2, ctx(a), ctx(b)))
  )

  case object RuleIntroductionLeftNot extends RuleIntroduction(
    ** |- *(a),
    *(!a) |- **,
    (bot, ctx) => IndexedSeq(LeftNot(bot, -1, ctx(a)))
  )

  case object RuleIntroductionRightNot extends RuleIntroduction(
    *(a) |- **,
    ** |- *(!a),
    (bot, ctx) => IndexedSeq(RightNot(bot, -1, ctx(a)))
  )

  case object RuleIntroductionRightRefl extends RuleIntroduction(
    __,
    ** |- *(s === s),
    (bot, ctx) => IndexedSeq(RightRefl(bot, ctx(s) === ctx(s)))
  )

  // Substitution

  case object RuleIntroductionLeftForall extends RuleIntroduction(
    *(p(t)) |- **,
    *(forall(x, p(x))) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val px = substituteVariables(fBody, Map(fArgs.head -> VariableTerm(ctx(x))))
      IndexedSeq(
        LeftForall(bot, -1, px, ctx(x), ctx(t))
      )
    }
  )

  case object RuleIntroductionRightForall extends RuleIntroduction(
    ** |- *(p(x)),
    ** |- *(forall(x, p(x))),
    (bot, ctx) => {
      // TODO x not already free in sequent; needs to be handled in `Rule`
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val px = substituteVariables(fBody, Map(fArgs.head -> VariableTerm(ctx(x))))
      IndexedSeq(
        RightForall(bot, -1, px, x)
      )
    }
  )

  case object RuleIntroductionLeftExists extends RuleIntroduction(
    *(p(x)) |- **,
    *(exists(x, p(x))) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val px = substituteVariables(fBody, Map(fArgs.head -> VariableTerm(ctx(x))))
      IndexedSeq(
        LeftExists(bot, -1, px, x)
      )
    }
  )

  case object RuleIntroductionRightExists extends RuleIntroduction(
    ** |- *(p(t)),
    ** |- *(exists(x, p(x))),
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val px = substituteVariables(fBody, Map(fArgs.head -> VariableTerm(ctx(x))))
      IndexedSeq(
        RightExists(bot, -1, px, ctx(x), ctx(t))
      )
    }
  )

  case object RuleIntroductionLeftExistsOne extends RuleIntroduction(
    *(exists(y, exists(x, (x === y) <=> p(x)))) |- **,
    *(existsOne(x, p(x))) |- **,
    (bot, ctx) => {
      // TODO y not free in p
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val px = substituteVariables(fBody, Map(fArgs.head -> VariableTerm(ctx(x))))
      ???
    }
  )

  // RuleIntroductionLeftExistsOne

  case object RuleIntroductionLeftSubstEq extends RuleIntroduction(
    *(p(s)) |- **,
    *(s === t, p(t)) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(fBody).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = substituteVariables(fBody, Map(fArgs.head -> label()))
      IndexedSeq(
        LeftSubstEq(bot, -1, ctx(s), ctx(t), ps, label)
      )
    }
  )

  case object RuleIntroductionRightSubstEq extends RuleIntroduction(
    ** |- *(p(s)),
    *(s === t) |- *(p(t)),
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(p)
      val taken = schematicFunctionsOf(fBody).map(_.id)
      val label = SchematicFunctionLabel[0](freshId(taken, "f"))
      val ps = substituteVariables(fBody, Map(fArgs.head -> label()))
      IndexedSeq(
        RightSubstEq(bot, -1, ctx(s), ctx(t), ps, label)
      )
    }
  )

  case object RuleIntroductionLeftSubstIff extends RuleIntroduction(
    *(f(a)) |- **,
    *(a <=> b, f(b)) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(f)
      IndexedSeq(
        LeftSubstIff(bot, -1, ctx(a), ctx(b), fBody, fArgs.head)
      )
    }
  )

  case object RuleIntroductionRightSubstIff extends RuleIntroduction(
    ** |- *(f(a)),
    *(a <=> b) |- *(f(b)),
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(f)
      IndexedSeq(
        RightSubstIff(bot, -1, ctx(a), ctx(b), fBody, fArgs.head)
      )
    }
  )

  //

  case object RuleSubstituteRightIff extends RuleIntroduction(
    (** |- *(f(a))) :+ ($$ |- $(a <=> b)),
    ** |- *(f(b)),
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(f)
      IndexedSeq(
        RightSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), fBody, fArgs.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  case object RuleSubstituteLeftIff extends RuleIntroduction(
    (*(f(a)) |- **) :+ ($$ |- $(a <=> b)),
    *(f(b)) |- **,
    (bot, ctx) => {
      val (fBody, fArgs) = ctx.applyMultiary(f)
      IndexedSeq(
        LeftSubstIff(bot +< (ctx(a) <=> ctx(b)), -1, ctx(a), ctx(b), fBody, fArgs.head),
        Cut(bot, -2, 0, ctx(a) <=> ctx(b))
      )
    }
  )

  // Elimination

  case object RuleCut extends RuleElimination(
    (** |- *(a)) :+ (*(a) |- **),
    ** |- **,
    (bot, ctx) => IndexedSeq(Cut(bot, -1, -2, ctx(a)))
  )

  case object RuleIntroductionLeftRefl extends RuleElimination(
    *(s === s) |- **,
    ** |- **,
    (bot, ctx) => IndexedSeq(LeftRefl(bot, -1, ctx(s) === ctx(s)))
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

  case object RuleModusPonens extends RuleElimination(
    (** |- *(a)) :+ ($(a) |- $(b)),
    ** |- *(b),
    (bot, ctx) => {
      IndexedSeq(
        Cut(bot, -1, -2, ctx(a)),
      )
    }
  )

  // Aliases

  val introHypo: RuleHypothesis.type = RuleHypothesis
  val introLAnd: RuleIntroductionLeftAnd.type = RuleIntroductionLeftAnd
  val introRAnd: RuleIntroductionRightAnd.type = RuleIntroductionRightAnd
  val introLOr: RuleIntroductionLeftOr.type = RuleIntroductionLeftOr
  val introROr: RuleIntroductionRightOr.type = RuleIntroductionRightOr
  val introLImp: RuleIntroductionLeftImplies.type = RuleIntroductionLeftImplies
  val introRImp: RuleIntroductionRightImplies.type = RuleIntroductionRightImplies
  val introLIff: RuleIntroductionLeftIff.type = RuleIntroductionLeftIff
  val introRIff: RuleIntroductionRightIff.type = RuleIntroductionRightIff
  val introLNot: RuleIntroductionLeftNot.type = RuleIntroductionLeftNot
  val introRNot: RuleIntroductionRightNot.type = RuleIntroductionRightNot
  val introRRefl: RuleIntroductionRightRefl.type = RuleIntroductionRightRefl
  val introLForall: RuleIntroductionLeftForall.type = RuleIntroductionLeftForall
  val introRForall: RuleIntroductionRightForall.type = RuleIntroductionRightForall
  val introLExists: RuleIntroductionLeftExists.type = RuleIntroductionLeftExists
  val introRExists: RuleIntroductionRightExists.type = RuleIntroductionRightExists
  val introLSubstEq: RuleIntroductionLeftSubstEq.type = RuleIntroductionLeftSubstEq
  val introRSubstEq: RuleIntroductionRightSubstEq.type = RuleIntroductionRightSubstEq
  val introLSubstIff: RuleIntroductionLeftSubstIff.type = RuleIntroductionLeftSubstIff
  val introRSubstIff: RuleIntroductionRightSubstIff.type = RuleIntroductionRightSubstIff
  // RuleIntroductionLeftExistsOne & RuleIntroductionRightExistsOne

  val elimCut: RuleCut.type = RuleCut
  val elimLRefl: RuleIntroductionLeftRefl.type = RuleIntroductionLeftRefl
  

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
