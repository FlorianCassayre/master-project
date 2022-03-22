package masterproject.front.proof.state

import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.SCSubproof
import masterproject.front.fol.FOL.*

trait ProofEnvironmentDefinitions extends ProofStateDefinitions {

  import scala.collection.mutable

  class ProofEnvironment(private[ProofEnvironmentDefinitions] val proven: mutable.Map[Sequent, (IndexedSeq[Sequent], SCProof)] = mutable.Map.empty) extends ReadableProofEnvironment {
    override def contains(sequent: Sequent): Boolean = proven.contains(sequent)
    def mkTheorem(proof: Proof): Theorem = {
      require(proof.initialState.goals.sizeIs == 1, "The proof must start with exactly one goal")
      val sequent = proof.initialState.goals.head
      reconstructSCProof(proof, this) match {
        case Some((scProof, theoremImports)) =>
          require(scProof.imports.size == theoremImports.size, "All imports must have been proven")
          proven.addOne((sequent, (scProof.imports.indices.map(theoremImports), scProof)))
          Theorem(this, sequent)
        case None => throw new Exception
      }
    }
    override def toString: String = proven.keySet.toSeq.map(new Theorem(this, _)).map(_.toString).mkString("\n")
  }

  case class Theorem private[ProofEnvironmentDefinitions](private[ProofEnvironmentDefinitions] val context: ProofEnvironment, sequent: Sequent) {
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
    val context = theorem.context
    val sorted = topologicalSort(theorem.context.proven.view.mapValues(_._1.toSet).toMap.withDefaultValue(Set.empty)).reverse
    val sequentToIndex = sorted.zipWithIndex.toMap

    SCProof(sorted.map { sequent =>
      val (imports, proof) = context.proven(sequent)
      SCSubproof(proof, imports.map(sequentToIndex))
    }.toIndexedSeq)
  }

}
