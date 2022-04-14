package me.cassayre.florian.masterproject.test.front

import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker
import me.cassayre.florian.masterproject.front.{*, given}
import me.cassayre.florian.masterproject.front.theory.SetTheory.*

@main def tests4(): Unit = {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  given ProofEnvironment = newSetTheoryEnvironment()

  val axExt: Axiom = axiomExtensionality.asJustified

  // Here we take advantage of forward mode to derive an axiom into a different theorem
  val axExtS: Theorem = {
    val t0 = elimRForallS(
      RuleForwardParametersBuilder
        .withPredicate(Notations.p, x => forall(y, forall(z, (z in x) <=> (z in y)) <=> (x === y)))
        .withFunction(Notations.t, s())
    )(axExt).get

    val t1 = elimRForallS(
      RuleForwardParametersBuilder
        .withPredicate(Notations.p, y => forall(z, (z in s) <=> (z in y)) <=> (s === y))
        .withFunction(Notations.t, t())
    )(t0).get

    t1.display()
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(axExtS)))
  println()

  // The following proofs are done in backward mode

  val thmEqSym: Theorem = {
    val proofMode = ProofMode((s === t) |- (t === s))
    import proofMode.*

    apply(rewrite((s === t) |- (s === t)))
    apply(introHypo)

    asTheorem()
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thmEqSym)))
  println()

  val thmEqTrans: Theorem = {
    val proofMode = ProofMode((s === t, t === u) |- (s === u))
    import proofMode.*

    apply(elimRSubstEq(
      RuleBackwardParametersBuilder
        .withPredicate(Notations.p, _ === u)
        .withFunction(Notations.s, t())
        .withFunction(Notations.t, s())
    ))
    apply(introHypo)
    apply(rewrite(right = Map(0 -> (s === t))))
    apply(introHypo)

    asTheorem()
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thmEqTrans)))
  println()

  /*
      apply(elimCut(
      RuleBackwardParametersBuilder.
        withPredicate(Notations.a, forall(z, (z in s) <=> (z in t)))
    ))
    focus(1)
    apply(introLSubstEq(
      RuleBackwardParametersBuilder.
        withPredicate(Notations.p, x => forall(z, (z in s) <=> (z in x)))
    ))
  */

  /*val theorem2 = {
    val proofMode = ProofMode(((s === t) /\ (t === u)) |- (s === u))
    import proofMode.*

    apply(introLAnd)
  }*/

}
