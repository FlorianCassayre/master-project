package masterproject.front.proof.state

import lisa.kernel.proof.{SCProof, SCProofChecker}
import lisa.kernel.proof.SequentCalculus.SCSubproof
import masterproject.front.fol.FOL.*

trait ProofEnvironmentDefinitions extends ProofStateDefinitions {

  import scala.collection.mutable

  class ProofEnvironment(private[ProofEnvironmentDefinitions] val proven: mutable.Map[Sequent, (IndexedSeq[Sequent], SCProof)] = mutable.Map.empty) extends ReadableProofEnvironment {
    override def contains(sequent: Sequent): Boolean = proven.contains(sequent)
    private def addSequentToEnvironment(sequent: Sequent, scProof: SCProof, theoremImports: Map[Int, Sequent]): Theorem = {
      require(scProof.imports.size == theoremImports.size && scProof.imports.indices.forall(theoremImports.contains),
        "All imports must have been proven")
      require(!proven.contains(sequent), "This sequent already has a proof") // Should we disallow that?
      assert(lisa.kernel.proof.SequentCalculus.isSameSequent(sequentToKernel(sequent), scProof.conclusion),
        "Error: the proof conclusion does not match the provided sequent")
      assert(SCProofChecker.checkSCProof(scProof).isValid,
        "Error: the theorem was found to produce an invalid proof; this could indicate a problem with a tactic or a bug in the implementation")
      proven.addOne((sequent, (scProof.imports.indices.map(theoremImports), scProof)))
      Theorem(this, sequent)
    }
    def mkTheorem(proof: Proof): Theorem = {
      require(proof.initialState.goals.sizeIs == 1, "The proof must start with exactly one goal")
      val sequent = proof.initialState.goals.head
      reconstructSCProof(proof, this) match {
        case Some((scProof, theoremImports)) => addSequentToEnvironment(sequent, scProof, theoremImports)
        case None => throw new Exception
      }
    }
    private[state] def mkTheorem(sequent: Sequent, scProof: SCProof, theorems: IndexedSeq[Theorem]): Theorem =
      addSequentToEnvironment(sequent, scProof, theorems.map(_.sequent).zipWithIndex.map(_.swap).toMap)
    override def toString: String = proven.keySet.toSeq.map(Theorem(this, _)).map(_.toString).mkString("\n")
  }

  case class Theorem private[ProofEnvironmentDefinitions](private[proof] val environment: ProofEnvironment, sequent: Sequent) {
    def asKernel: lisa.kernel.proof.SequentCalculus.Sequent = sequentToKernel(sequent)
    override def toString: String = s"Theorem: $sequent"
  }


  private def topologicalSort[U](adjacency: Map[U, Set[U]]): Seq[U] = {
    def dfs(stack: Seq[(U, Set[U])], marks: Map[U, Boolean], remaining: Set[U], sorted: Seq[U]): (Map[U, Boolean], Set[U], Seq[U]) = {
      stack match {
        case (u, adjacent) +: tail =>
          adjacent.headOption match {
            case Some(v) =>
              marks.get(v) match {
                case Some(false) => throw new Exception // Cycle
                case Some(true) => dfs((u, adjacent.tail) +: tail, marks, remaining, sorted)
                case None => dfs((v, adjacency.getOrElse(v, Set.empty[U])) +: (u, adjacent.tail) +: tail, marks + (v -> false), remaining, sorted)
              }
            case None => dfs(tail, marks + (u -> true), remaining - u, u +: sorted)
          }
        case _ => (marks, remaining, sorted)
      }
    }
    def iterate(marks: Map[U, Boolean], remaining: Set[U], sorted: Seq[U]): Seq[U] = {
      if(remaining.nonEmpty) {
        val u = remaining.head
        val (newMarks, newRemaining, newSorted) = dfs(Seq((u, adjacency.getOrElse(u, Set.empty[U]))), marks + (u -> false), remaining - u, sorted)
        iterate(newMarks, newRemaining, newSorted)
      } else {
        sorted
      }
    }
    iterate(Map.empty, adjacency.keySet ++ adjacency.values.flatten, Seq.empty)
  }

  def reconstructSCProofForTheorem(theorem: Theorem): SCProof = {
    // Inefficient, no need to traverse/reconstruct the whole graph
    val context = theorem.environment
    val sorted = topologicalSort(theorem.environment.proven.view.mapValues(_._1.toSet).toMap.withDefaultValue(Set.empty)).reverse
    val sequentToIndex = sorted.zipWithIndex.toMap

    SCProof(sorted.map { sequent =>
      val (imports, proof) = context.proven(sequent)
      SCSubproof(proof, imports.map(sequentToIndex))
    }.toIndexedSeq)
  }

}
