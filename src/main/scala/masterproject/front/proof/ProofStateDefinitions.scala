package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.Unification.*
import lisa.kernel.proof.SequentCalculus.SCProofStep

trait ProofStateDefinitions extends SequentDefinitions {

  final case class ProofState(goals: IndexedSeq[Sequent]) {
    override def toString: String =
      ((if (goals.nonEmpty) s"${goals.size} goal${if (goals.sizeIs > 1) "s" else ""}" else "[zero goals]") +:
        goals.map(_.toString)
        ).mkString("\n")
  }

  abstract class Rule {
    def hypotheses: IndexedSeq[PartialSequent]
    def conclusion: PartialSequent

    // The premises indexing is implicit:
    // * 0, 1, 2 will reference respectively the first, second and third steps in that array
    // * -1, -2, -3 will reference respectively the first second and third premises, as returned by `hypotheses`
    def reconstruct(bot: Sequent, ctx: UnificationContext): IndexedSeq[SCProofStep]

    private def partials: Seq[PartialSequent] = hypotheses :+ conclusion

    require(partials.forall(isSequentWellFormed))
    require(partials.flatMap(_.formulas).flatMap(f => predicatesOf(f) ++ functionsOf(f)).forall(_.arity == 0))

    override def toString: String = {
      val top = hypotheses.map(_.toString).mkString(" " * 6)
      val bottom = conclusion.toString
      val length = Math.max(top.length, bottom.length)

      def pad(s: String): String = " " * ((length - s.length) / 2) + s

      Seq(pad(top), "=" * length, pad(bottom)).mkString("\n")
    }
  }

}
