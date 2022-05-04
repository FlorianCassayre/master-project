package me.cassayre.florian.masterproject.test.front

import lisa.kernel.Printer

import scala.util.chaining.*
import me.cassayre.florian.masterproject.front.{*, given}

@main def tests6(): Unit = {
  import me.cassayre.florian.masterproject.front.theory.SetTheory.*

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s: SchematicFunctionLabel[0], t: SchematicFunctionLabel[0], u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
  val (x: VariableLabel, y, z) = (VariableLabel("x"), me.cassayre.florian.masterproject.front.fol.FOL.VariableLabel("y"), VariableLabel("z"))

  given ProofEnvironment = newSetTheoryEnvironment()

  val axExt: Axiom = axiomExtensionality.asJustified.display()
  val axEmpty: Axiom = axiomEmpty.asJustified.display()
  val axUnion: Axiom = axiomUnion.asJustified.display()

  // 1. Generalize universal quantifiers

  val thmExtSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters().withFunction(Notations.t, s()))(axExt).get
    val t1 = elimRForallS(RuleParameters().withFunction(Notations.t, t()))(t0).get
    t1
  }.display()

  val thmEmptySchema: Theorem = elimRForallS(
    RuleParameters()
      .withPredicate(Notations.p, x => !(x in emptySet))
      .withFunction(Notations.t, s())
  )(axEmpty).get.display()

  val thmUnionSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters().withFunction(Notations.t, s()))(axUnion).get
    val t1 = elimRForallS(RuleParameters().withFunction(Notations.t, t()))(t0).get
    t1
  }.display()

  // 2. Write the proof

  val thmUnionEmpty = {
    val p = ProofMode(() |- unionSet(emptySet) === emptySet)
    import p.*

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"forall z. (z in U({})) <=> (z in {})")
    ))

    focus(1)
    val _ = thmExtSchema(Notations.s, unionSet(emptySet): Term)(Notations.t, emptySet: Term).display()
    apply(justification) // Uses the previously proved theorem

    apply(introRForallS(RuleParameters().withFunction(Notations.t, s())))

    apply(RuleSubstituteRightIff(
      RuleParameters()
        .withConnector(Notations.f, x => x <=> (s in emptySet))
        .withPredicate(Notations.a, formula"exists y. (?s in y) /\ (y in {})")
    ))

    focus(1)
    val _ = thmUnionSchema(t, emptySet: Term).rewrite(state.goals.head).get.display()
    apply(justification)

    apply(introRIff)
    apply(introRImp)
    apply(introLExists(RuleParameters().withVariable(x, y)))
    apply(introLAnd)
    apply(weaken(left = Set(0), right = Set(0)))
    apply(elimRNot)
    val _ = thmEmptySchema(s, me.cassayre.florian.masterproject.front.fol.FOL.VariableTerm(y)).display()
    apply(justification)

    apply(introRImp)
    apply(weaken(right = Set(0)))
    apply(elimRNot)
    apply(justification)

    asTheorem() // |- U({}) = {}
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thmUnionEmpty)))

}
