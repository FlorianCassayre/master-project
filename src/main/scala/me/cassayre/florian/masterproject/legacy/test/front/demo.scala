package me.cassayre.florian.masterproject.legacy.test.front

import lisa.kernel.Printer

import scala.util.chaining.*
import me.cassayre.florian.masterproject.front.{*, given}

// `sbt console`

@main def demo1(): Unit = {
  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))

  given ProofEnvironment = newEmptyEnvironment()

  val p1 = ProofMode(a |- b ==> (a /\ b))
  p1.apply(introRImp)
  p1.apply(introRAnd)
  p1.apply(introHypo)
  p1.apply(introHypo)
  val thm = p1.asTheorem()

  val thm2 = thm.rewrite(a |- b ==> (b /\ a)).display()
  val thm3 = thm2(AssignedPredicate(a, b())).display()

  def autoProp = (introHypo
    | introLAnd | introRAnd
    | introLOr | introROr
    | introLImp | introRImp
    | introLIff | introRIff
    | introLNot | introRNot).+

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thm3)))
}

@main def demo2(): Unit = {
  import me.cassayre.florian.masterproject.front.theory.SetTheory.*

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  given ProofEnvironment = newSetTheoryEnvironment()

  // Symmetry

  val thmEqSym: Theorem = {
    val proofMode = ProofMode((s === t) |- (t === s))
    import proofMode.*

    apply(rewrite((s === t) |- (s === t)))
    apply(introHypo)

    asTheorem()
  }

  // Transitivity

  val thmEqTrans: Theorem = {
    val proofMode = ProofMode((s === t, t === u) |- (s === u))
    import proofMode.*

    apply(elimRSubstEq(
      RuleParameters()
        .withPredicate(Notations.p, _ === u)
        .withFunction(Notations.s, t())
        .withFunction(Notations.t, s())
    ))
    apply(introHypo)
    apply(rewrite(right = Map(0 -> (s === t))))
    apply(introHypo)

    asTheorem()
  }

  // Theorem application (backward)

  val xySym = {
    val proofMode = ProofMode(() |- (x === y) <=> (y === x))
    import proofMode.*

    // Bring these facts in context
    val thm1 = thmEqSym(AssignedFunction(s, VariableTerm(x)))(AssignedFunction(t, VariableTerm(y)))
    val thm2 = thmEqSym(AssignedFunction(s, VariableTerm(y)))(AssignedFunction(t, VariableTerm(x)))

    apply((introRIff | introRImp | justification(thm1) | justification(thm2)).+)

    asTheorem()
  }

  // Transform an axiom

  val axEmpty: Axiom = axiomEmpty.asJustified.display()

  val thmEmptySchema: Theorem = elimRForallS(
    RuleParameters()
      .withPredicate(Notations.p, x => !(x in emptySet))
      .withFunction(Notations.t, s())
  )(axEmpty).get.display()

  val xNotInEmptyThm = thmEmptySchema(AssignedFunction(s, VariableTerm(x))).display()

  println(Printer.prettySCProof(reconstructSCProofForTheorem(xNotInEmptyThm)))
}
