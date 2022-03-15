package masterproject.front

import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))

  val initialProofState = ProofState(
    IndexedSeq(
      Sequent(
        IndexedSeq(c),
        IndexedSeq(a),
      )
    )
  )

  val appliedRules: Seq[TacticApplication] = Seq(
    TacticApplication(
      RuleModusPonens,
      predicates = Map(Notations.a -> (a /\ b)),
    ),
    TacticApplication(
      TacticApplyTheorem,
    ),
  )

  println(initialProofState)
  println()
  println(appliedRules.map(_.tactic).mkString("\n\n"))
  println()

  val universalContext = new ReadableProofContext {
    override def contains(sequent: Sequent): Boolean = true
  }

  val reconstructed = reconstructSCProof(Proof(initialProofState, appliedRules), universalContext)

  reconstructed match {
    case Some((proof, theorems)) =>
      val judgement = SCProofChecker.checkSCProof(proof)

      println(Printer.prettySCProof(proof, judgement))

      println()
      if(theorems.nonEmpty) {
        val keys = theorems.keySet.toSeq.sorted
        println(s"Imports that are theorems: ${keys.mkString(", ")} (steps number ${keys.map(i => -(i + 1)).mkString(", ")})")
        println()
      }

      if(judgement.isValid) {
        if(proof.imports.nonEmpty) {
          println(s"Warning, the proof contains ${proof.imports.size} import(s)")
          println()
        }
        println("The proof is valid")
      } else {
        println("!!! ERROR !!! The proof is invalid")
      }
    case None =>
      println("Failed to apply a rule and/or reconstruct the proof")
  }

}
