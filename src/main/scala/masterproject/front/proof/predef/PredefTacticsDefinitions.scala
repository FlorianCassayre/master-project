package masterproject.front.proof.predef

import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import masterproject.front.proof.state.ProofStateDefinitions

trait PredefTacticsDefinitions extends ProofStateDefinitions {

  case object GeneralTacticSolver extends GeneralTactic {
    import Notations.*

    override def apply(proofGoal: Sequent, app: TacticParameters): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      val steps = SimplePropositionalSolver.solveSequent(proofGoal).steps
      Some((IndexedSeq.empty, () => steps))
    }
  }

  case object GeneralTacticRightIff extends GeneralTactic {
    import Notations.*

    override def apply(proofGoal: Sequent, app: TacticParameters): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      app.formulas.collect { case (IndexedSeq(), IndexedSeq(i)) if proofGoal.right.indices.contains(i) =>
        val formula = proofGoal.right(i)
        val ea = instantiatePredicateSchemas(app.predicates(c), Map(e -> (app.predicates(a), Seq.empty)))
        val eb = instantiatePredicateSchemas(app.predicates(c), Map(e -> (app.predicates(b), Seq.empty)))
        if(formula == eb) { // TODO isSame
          val bot: lisa.kernel.proof.SequentCalculus.Sequent = proofGoal
          Some(
            IndexedSeq(
              proofGoal.copy(right = (proofGoal.right.take(i) :+ ea) ++ proofGoal.right.drop(i + 1)),
              () |- app.predicates(a) <=> app.predicates(b),
            ),
            () =>
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

}
