package masterproject.front.proof.predef

import masterproject.front.fol.FOL.*
import masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import masterproject.front.proof.state.ProofStateDefinitions

trait PredefTacticsDefinitions extends ProofStateDefinitions {

  case object GeneralTacticSolver extends GeneralTactic {
    import Notations.*

    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructGeneral)] = {
      val steps = SimplePropositionalSolver.solveSequent(proofGoal).steps
      Some((IndexedSeq.empty, () => steps))
    }
  }

}
