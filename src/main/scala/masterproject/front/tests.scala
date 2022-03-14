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
        IndexedSeq(a \/ b),
      )
    )
  )

  val appliedRules: Seq[TacticApplication] = Seq(
    TacticApplication(
      GeneralTacticRightIff,
      predicates = Map(Notations.a -> c, Notations.b -> b, Notations.c -> a \/ Notations.e),
      formulas = Some((IndexedSeq.empty, IndexedSeq(0)))
    ),
  )

  println(initialProofState)
  println()
  println(appliedRules.map(_.tactic).mkString("\n\n"))
  println()

  val reconstructed = reconstructSCProof(initialProofState, appliedRules)

  reconstructed match {
    case Some(proof) =>
      val judgement = SCProofChecker.checkSCProof(proof)

      println(Printer.prettySCProof(proof, judgement))

      println()

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
