package me.cassayre.florian.masterproject.legacy.test.front

import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker
import me.cassayre.florian.masterproject.front.{*, given}

@main def tests2(): Unit = {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))

  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))

  given ctx: ProofEnvironment = newEmptyEnvironment()

  val fproof1 = Proof(
    ProofState(
      IndexedSeq(
        Sequent(
          IndexedSeq(),
          IndexedSeq((a /\ b) <=> (b /\ a)),
        )
      )
    ),
    Seq(
      TacticSolverNative,
    )
  )

  val thm1 = ctx.mkTheorem(fproof1)

  val fproof2 = Proof(
    ProofState(
      IndexedSeq(
        Sequent(
          IndexedSeq(a /\ b),
          IndexedSeq(b /\ a),
        )
      )
    ),
    Seq[Tactic](
      RuleSubstituteRightIff(
        RuleParameters()
          .withPredicate(Notations.a, a /\ b)
          .withConnector(Notations.f, identity)
      ),
      RuleHypothesis(),
      TacticApplyJustification(thm1),
    )
  )

  val thm2 = ctx.mkTheorem(fproof2)

  val reconstructed = reconstructSCProofForTheorem(thm2)

  println(Printer.prettySCProof(reconstructed))

  assert(SCProofChecker.checkSCProof(reconstructed).isValid)

  println()
  println("The reconstructed proof is valid.")
}
