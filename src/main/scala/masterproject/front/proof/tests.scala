package masterproject.front.proof

import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val x = SchematicPredicateLabel[0]("x")

  val initialProofState = ProofState(
    IndexedSeq(
      Sequent(
        IndexedSeq(),
        IndexedSeq(a, b),
      )
    )
  )

  val appliedRules: Seq[TacticApplication] = Seq(
    TacticApplication(
      RuleEliminationRightOr,
      formulas = Some((IndexedSeq.empty, IndexedSeq(0, 1)))
    ),
  )

  println(initialProofState)
  println()
  println(appliedRules.map(_.tactic).mkString("\n\n"))
  println()

  val reconstructed = reconstructSCProof(initialProofState, appliedRules)

  reconstructed match {
    case Some(proof) =>
      val checkerResult = SCProofChecker.checkSCProof(proof)

      println(Printer.prettySCProof(proof, if(checkerResult._1) None else Some((checkerResult._2, checkerResult._3))))

      println()

      if(checkerResult._1) {
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
