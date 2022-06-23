package me.cassayre.florian.masterproject.examples

import me.cassayre.florian.masterproject.front.*
import lisa.kernel.proof.{SCProof, SCProofChecker}
import me.cassayre.florian.masterproject.front.printer.KernelPrinter

import scala.util.chaining.*

@main def frontSolver(): Unit = {

  val propositionalSolver: Tactic = (introHypo
    | introLAnd | introRAnd
    | introLOr | introROr
    | introLImp | introRImp
    | introLIff | introRIff
    | introLNot | introRNot).+

  def testSolve(sequent: Sequent): Unit = {
    given ProofEnvironment = newEmptyEnvironment()

    val theorem: Theorem = ProofMode(sequent).tap(_(propositionalSolver)).asTheorem()
    val scProof: SCProof = reconstructSCProofForTheorem(theorem)

    println(KernelPrinter.prettyJudgedProof(SCProofChecker.checkSCProof(scProof)))
  }

  testSolve(sequent"?a |- ?a")
  testSolve(sequent"|- (?a \/ ?b) => (!?a => ?b)")
  testSolve(sequent"|- (?a /\ (?b /\ ?c)) <=> ((?a /\ ?b) /\ ?c)")

}
