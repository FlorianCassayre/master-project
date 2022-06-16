package me.cassayre.florian.masterproject.legacy.test.front

import me.cassayre.florian.masterproject.front.{*, given}
import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker

@main def tests(): Unit = {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))

  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))

  val fproof = Proof(
    ProofState(
      IndexedSeq(
        Sequent(
          IndexedSeq(a /\ b),
          IndexedSeq(a),
        )
      )
    ),
    Seq(
      TacticSolverNative,
    )
  )

  println(fproof.initialState)
  println()
  println(fproof.steps.mkString("\n\n"))
  println()

  val universalContext = newEmptyEnvironment()

  val reconstructed = evaluateProof(fproof)(universalContext).map(reconstructSCProof)

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
