package me.cassayre.florian.masterproject.examples

import lisa.kernel.proof.SCProofChecker

import scala.util.chaining.*
import me.cassayre.florian.masterproject.front.fol.FOL.{*, given}
import me.cassayre.florian.masterproject.front.proof.Proof.{*, given}
import me.cassayre.florian.masterproject.front.parser.FrontMacro.{*, given}
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter.*
import me.cassayre.florian.masterproject.front.printer.{FrontPrintStyle, KernelPrinter}
import me.cassayre.florian.masterproject.front.theory.SetTheory.*

@main def frontInteractiveProof1(): Unit = {
  val s = SchematicFunctionLabel[0]("s")

  // The first step is to provide the global environment, i.e. the underlying theory
  given ProofEnvironment = newSetTheoryEnvironment()

  val t0: Theorem = {
    // To enter proof mode, the user should specify the conclusion of the fact to prove
    val p = ProofMode(sequent"|- (!?a \/ ?b) <=> (?a => ?b)")
    import p.*

    // Then they should apply tactics to update and eventually eliminate the goals
    apply(introRIff)
    apply(introRImp)
    apply(introRImp)
    apply(introLOr)
    apply(introLNot)
    apply(introHypo)
    apply(introHypo)

    apply(introRImp)
    apply(introROr)
    apply(introLImp)
    apply(introRNot)
    apply(introHypo)

    apply(introHypo)

    // Once all the goals are eliminated, this method can be called to obtain a theorem
    asTheorem()
  }
  // Note: this proof could in fact be made shorter, see `frontSolver`

  // Axioms act as proven theorems, except that no proof is needed to use them
  val axEmpty: Axiom = axiomEmpty.asJustified.display()

  val t1: Theorem = {
    val p = ProofMode(sequent"|- ({} in {}) => ?a")

    p.apply(introRImp)
    p.apply(elimRNot)
    // Here we implicitly instantiate the axiom to match our goal
    p.apply(justificationInst(
      elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axEmpty).get
    ))

    p.asTheorem()
  }

  println("=== Reconstruction ===")
  println("(t0):")
  println(KernelPrinter.prettyJudgedProof(SCProofChecker.checkSCProof(reconstructSCProofForTheorem(t0))))
  println()
  println("(t1):")
  println(KernelPrinter.prettyJudgedProof(SCProofChecker.checkSCProof(reconstructSCProofForTheorem(t1))))
}
