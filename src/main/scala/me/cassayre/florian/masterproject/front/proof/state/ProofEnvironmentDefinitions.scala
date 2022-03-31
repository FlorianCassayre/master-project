package me.cassayre.florian.masterproject.front.proof.state

import lisa.kernel.Printer
import lisa.kernel.proof.{RunningTheory, SCProof, SCProofChecker}
import lisa.kernel.proof.SequentCalculus.{SCSubproof, sequentToFormula}
import me.cassayre.florian.masterproject.front.fol.FOL.*

trait ProofEnvironmentDefinitions extends ProofStateDefinitions {

  import scala.collection.mutable

  final class ProofEnvironment private[front] (
    private[ProofEnvironmentDefinitions] val runningTheory: RunningTheory,
    private[ProofEnvironmentDefinitions] val proven: mutable.Map[Sequent, (IndexedSeq[Sequent], SCProof)] = mutable.Map.empty,
  ) extends ReadableProofEnvironment {
    override def contains(sequent: Sequent): Boolean = proven.contains(sequent)
    private def addSequentToEnvironment(sequent: Sequent, scProof: SCProof, justifiedImports: Map[Int, Sequent]): Theorem = {
      require(scProof.imports.size == justifiedImports.size && scProof.imports.indices.forall(justifiedImports.contains),
        "All imports must be justified")
      require(!proven.contains(sequent), "This sequent already has a proof") // Should we disallow that?
      assert(lisa.kernel.proof.SequentCalculus.isSameSequent(sequentToKernel(sequent), scProof.conclusion),
        "Error: the proof conclusion does not match the provided sequent")
      val judgement = SCProofChecker.checkSCProof(scProof)
      if(!judgement.isValid) {
        throw new AssertionError(
          Seq(
            "Error: the theorem was found to produce an invalid proof; this could indicate a problem with a tactic or a bug in the implementation",
            "The produced proof is shown below for reference:",
            Printer.prettySCProof(scProof, judgement)
          ).mkString("\n")
        )
      }
      proven.addOne((sequent, (scProof.imports.indices.map(justifiedImports), scProof)))
      Theorem(this, sequent)
    }
    def mkTheorem(proof: Proof): Theorem = {
      require(proof.initialState.goals.sizeIs == 1, "The proof must start with exactly one goal")
      val sequent = proof.initialState.goals.head
      evaluateProof(proof)(this).map(reconstructSCProof) match {
        case Some((scProof, theoremImports)) => addSequentToEnvironment(sequent, scProof, theoremImports)
        case None => throw new Exception
      }
    }
    def mkAxiom(formula: Formula): Axiom = {
      require(runningTheory.isAxiom(formula))
      Axiom(this, formula)
    }
    //def mkDefinition() // TODO
    private[proof] def mkTheorem(sequent: Sequent, scProof: SCProof, theorems: IndexedSeq[Justified]): Theorem =
      addSequentToEnvironment(sequent, scProof, theorems.map(_.sequent).zipWithIndex.map(_.swap).toMap)
    //override def toString: String = proven.keySet.toSeq.map(Theorem(this, _)).map(_.toString).mkString("\n")
  }

  def newEmptyEnvironment(): ProofEnvironment = new ProofEnvironment(new RunningTheory)

  sealed abstract class Justified {
    private[proof] val environment: ProofEnvironment
    def sequent: Sequent
    final def sequentAsKernel: lisa.kernel.proof.SequentCalculus.Sequent = sequentToKernel(sequent)
  }

  case class Axiom private[ProofEnvironmentDefinitions](private[proof] val environment: ProofEnvironment, formula: Formula) extends Justified {
    override def sequent: Sequent = () |- formula
    override def toString: String = s"Axiom: $sequent"
  }

  case class Theorem private[ProofEnvironmentDefinitions](private[proof] val environment: ProofEnvironment, sequent: Sequent) extends Justified {
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
