package masterproject

import lisa.kernel.proof.SequentCalculus.*

object SCUtils {

  def mapPremises(step: SCProofStep, mapping: Int => Int): SCProofStep = step match {
    case s: Rewrite => s.copy(t1 = mapping(s.t1))
    case s: Hypothesis => s
    case s: Cut => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftAnd => s.copy(t1 = mapping(s.t1))
    case s: LeftOr => s.copy(t = s.t.map(mapping))
    case s: LeftImplies => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: LeftIff => s.copy(t1 = mapping(s.t1))
    case s: LeftNot => s.copy(t1 = mapping(s.t1))
    case s: LeftForall => s.copy(t1 = mapping(s.t1))
    case s: LeftExists => s.copy(t1 = mapping(s.t1))
    case s: LeftExistsOne => s.copy(t1 = mapping(s.t1))
    case s: RightAnd => s.copy(t = s.t.map(mapping))
    case s: RightOr => s.copy(t1 = mapping(s.t1))
    case s: RightImplies => s.copy(t1 = mapping(s.t1))
    case s: RightIff => s.copy(t1 = mapping(s.t1), t2 = mapping(s.t2))
    case s: RightNot => s.copy(t1 = mapping(s.t1))
    case s: RightForall => s.copy(t1 = mapping(s.t1))
    case s: RightExists => s.copy(t1 = mapping(s.t1))
    case s: RightExistsOne => s.copy(t1 = mapping(s.t1))
    case s: Weakening => s.copy(t1 = mapping(s.t1))
    case s: LeftRefl => s.copy(t1 = mapping(s.t1))
    case s: RightRefl => s
    case s: LeftSubstEq => s.copy(t1 = mapping(s.t1))
    case s: RightSubstEq => s.copy(t1 = mapping(s.t1))
    case s: LeftSubstIff => s.copy(t1 = mapping(s.t1))
    case s: RightSubstIff => s.copy(t1 = mapping(s.t1))
    case s: SCSubproof => s.copy(premises = s.premises.map(mapping))
    case s: InstFunSchema => s.copy(t1 = mapping(s.t1))
    case s: InstPredSchema => s.copy(t1 = mapping(s.t1))
  }

}
