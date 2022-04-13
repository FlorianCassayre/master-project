package me.cassayre.florian.masterproject.test.front

import lisa.kernel.Printer
import me.cassayre.florian.masterproject.front.{*, given}
import me.cassayre.florian.masterproject.front.theory.SetTheory.*

@main def tests5(): Unit = {
  // This is the environment that will hold all the theorems we have proved so far
  given ProofEnvironment = newEmptyEnvironment()

  // Symbols
  val (a: SchematicPredicateLabel[0], b: SchematicPredicateLabel[0], c: SchematicPredicateLabel[0]) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (p: SchematicPredicateLabel[2]) = SchematicPredicateLabel[2]("p")
  val (x: SchematicFunctionLabel[0]) = SchematicFunctionLabel[0]("x")

  // A compound formula
  val f: Formula = a <=> b

  // A complete solver for propositional logic.
  // It is constructed from scratch using the different building blocks provided by the framework:
  // * Rules, that are implicitly converted to tactics with default arguments
  // * Pipe operator, allows a tactic to fall back to another in case it fails
  // * Repetition operator, apply a tactic as many times as possible
  val autoProp = (introHypo
    | introLAnd | introRAnd
    | introLOr | introROr
    | introLImp | introRImp
    | introLIff | introRIff
    | introLNot | introRNot).+

  // Note that this very tactic is already defined and available as `TacticPropositionalSolver`

  val theorem1 = {
    val proofMode = ProofMode(sequent"$f /\ ($p({}, $x) \/ !c) |- ($f /\ ${p(emptySet, x)}) \/ ((?a <=> ?b) /\ !c)")
    import proofMode.*

    apply(autoProp)

    // This method can only be called if there are no goals left
    asTheorem()
  }

  // Display the full SC proof
  println(Printer.prettySCProof(reconstructSCProofForTheorem(theorem1)))
}
