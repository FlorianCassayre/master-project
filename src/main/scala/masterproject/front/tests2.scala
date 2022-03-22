package masterproject.front

import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker
import masterproject.front.fol.FOL.*
import masterproject.front.proof.Proof.*

@main def tests2(): Unit = {

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))

  val ctx = new ProofContext

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
      TacticApplication(RulePropositionalSolver),
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
    Seq(
      TacticApplication(
        RuleSubstituteRightIff,
        predicates = Map(Notations.a -> (a /\ b)),
        connectors = Map(Notations.f -> (x, Seq(x)))
      ),
      TacticApplication(RuleHypothesis),
      TacticApplication(TacticApplyTheorem),
    )
  )

  val thm2 = ctx.mkTheorem(fproof2)

  val reconstructed = reconstructSCProofForTheorem(thm2)

  println(Printer.prettySCProof(reconstructed))

  assert(SCProofChecker.checkSCProof(reconstructed).isValid)

  println()
  println("The reconstructed proof is valid.")
}