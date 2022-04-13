package me.cassayre.florian.masterproject.front.proof.predef

trait PredefCombinedDefinitions extends PredefRulesDefinitions {

  val TacticPropositionalSolver: Tactic = TacticRepeat(TacticFallback(Seq(
    RuleHypothesis,
    RuleIntroductionLeftAnd, RuleIntroductionRightAnd,
    RuleIntroductionLeftOr, RuleIntroductionRightOr,
    RuleIntroductionLeftImplies, RuleIntroductionRightImplies,
    RuleIntroductionLeftIff, RuleIntroductionRightIff,
    RuleIntroductionLeftNot, RuleIntroductionRightNot,
  )))

}
