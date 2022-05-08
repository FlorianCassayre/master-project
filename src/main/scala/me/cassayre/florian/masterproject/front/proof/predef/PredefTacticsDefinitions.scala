package me.cassayre.florian.masterproject.front.proof.predef

import lisa.kernel.proof.SCProof
import me.cassayre.florian.masterproject.front.fol.FOL.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import me.cassayre.florian.masterproject.front.proof.state.ProofEnvironmentDefinitions

trait PredefTacticsDefinitions extends ProofEnvironmentDefinitions {

  case object TacticSolverNative extends TacticGoalFunctional {
    import Notations.*

    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      val steps = SimplePropositionalSolver.solveSequent(proofGoal).steps
      Some((IndexedSeq.empty, () => steps))
    }
  }

  case class TacticRewritePartial(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(left.keySet.forall(proofGoal.left.indices.contains) && right.keySet.forall(proofGoal.right.indices.contains)) {
        val rewritten = Sequent(
          proofGoal.left.indices.map(i => left.getOrElse(i, proofGoal.left(i))),
          proofGoal.right.indices.map(i => right.getOrElse(i, proofGoal.right(i)))
        )
        if(isSameSequent(proofGoal, rewritten)) {
          Some((IndexedSeq(rewritten), () => IndexedSeq(Rewrite(rewritten, -1))))
        } else {
          None
        }
      } else {
        None
      }
    }
  }

  case class TacticRewriteSequent(rewritten: Sequent) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(isSameSequent(proofGoal, rewritten)) {
        Some((IndexedSeq(rewritten), () => IndexedSeq(Rewrite(proofGoal, -1))))
      } else {
        None
      }
    }
  }

  object TacticalRewrite {
    def apply(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty): TacticRewritePartial =
      TacticRewritePartial(left, right)
    def apply(rewritten: Sequent): TacticRewriteSequent = TacticRewriteSequent(rewritten)
  }

  case class TacticWeakenPartial(left: Set[Int] = Set.empty, right: Set[Int] = Set.empty) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(left.forall(proofGoal.left.indices.contains) && right.forall(proofGoal.right.indices.contains)) {
        val weaker = Sequent(
          proofGoal.left.zipWithIndex.filter { case (_, i) => !left.contains(i) }.map { case (f, _) => f },
          proofGoal.right.zipWithIndex.filter { case (_, i) => !right.contains(i) }.map { case (f, _) => f }
        )
        Some((IndexedSeq(weaker), () => IndexedSeq(Weakening(proofGoal, -1))))
      } else {
        None
      }
    }
  }

  case class TacticWeakenSequent(weaker: Sequent) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      // This can be made powerful with a matching algorithm
      ???
    }
  }

  object TacticalWeaken {
    def apply(left: Set[Int] = Set.empty, right: Set[Int] = Set.empty): TacticWeakenPartial =
      TacticWeakenPartial(left, right)
    //def apply(weaker: Sequent): TacticWeakenSequent = TacticWeakenSequent(weaker)
  }

  case class TacticInstantiateFunctionSchema(sequent: Sequent, assigned: AssignedFunction) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      val map = Seq(assigned)
      val instantiated = Sequent(
        sequent.left.map(formula => instantiateFormulaSchemas(formula, functions = map)),
        sequent.right.map(formula => instantiateFormulaSchemas(formula, functions = map))
      )
      if(isSameSequent(proofGoal, instantiated)) {
        Some((
          IndexedSeq(sequent),
          () => IndexedSeq(InstFunSchema(proofGoal, -1, Map(toKernel(assigned.schema) -> assigned.lambda)))
        ))
      } else {
        None
      }
    }
  }

  extension (theorem: Theorem) {
    def apply(assigned: AssignedFunction): Theorem = {
      val map: Seq[AssignedFunction] = Seq(assigned)
      val replaced = Sequent(
        theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, functions = map)),
        theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, functions = map))
      )
      val scProof = SCProof(
        IndexedSeq(
          InstFunSchema(replaced, -1, Map(toKernel(assigned.schema) -> assigned.lambda))
        ),
        IndexedSeq(sequentToKernel(theorem.sequent))
      )
      theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem))
    }
    def apply(assigned: AssignedPredicate): Theorem = {
      val map: Seq[AssignedPredicate] = Seq(assigned)
      val replaced = Sequent(
        theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, predicates = map)),
        theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, predicates = map))
      )
      val scProof = SCProof(
        IndexedSeq(
          InstPredSchema(replaced, -1, Map(toKernel(assigned.schema) -> assigned.lambda))
        ),
        IndexedSeq(sequentToKernel(theorem.sequent))
      )
      theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem))
    }

    def rewrite(rewritten: Sequent): Theorem =
      TacticRewriteSequent(theorem.sequent).apply(rewritten).map { case (_, reconstruct) =>
        val scProof = SCProof(reconstruct(), IndexedSeq(sequentToKernel(theorem.sequent)))
        theorem.environment.mkTheorem(rewritten, scProof, IndexedSeq(theorem))
      }.get
  }

}
