package me.cassayre.florian.masterproject.test.front

import lisa.kernel.Printer

import scala.util.chaining.*
import me.cassayre.florian.masterproject.front.fol.FOL.{*, given}
import me.cassayre.florian.masterproject.front.proof.Proof.{*, given}
import me.cassayre.florian.masterproject.front.parser.FrontMacro.{*, given}
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter.*
import me.cassayre.florian.masterproject.front.theory.SetTheory.*

@main def tests6(): Unit = {

  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (s, t, u, v) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"), SchematicFunctionLabel[0]("v"))
  val (x, y, z) = (VariableLabel("x"), me.cassayre.florian.masterproject.front.fol.FOL.VariableLabel("y"), VariableLabel("z"))

  given ProofEnvironment = newSetTheoryEnvironment()

  val axExt: Axiom = axiomExtensionality.asJustified.display()
  val axEmpty: Axiom = axiomEmpty.asJustified.display()
  val axUnion: Axiom = axiomUnion.asJustified.display()
  val axPower: Axiom = axiomPower.asJustified.display()
  val defSubset: Axiom = definitionSubset.asJustified.display()

  // 1. Generalize universal quantifiers

  val thmExtSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axExt).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

  val thmEmptySchema: Theorem = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axEmpty).get.display()

  val thmUnionSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axUnion).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

  val thmPowerSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axPower).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

  val thmSubsetSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(defSubset).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

  // 2. Write the proof

  val thmUnionEmpty = {
    val p = ProofMode(() |- unionSet(emptySet) === emptySet)
    import p.*

    apply(elimRSubstIff(
      RuleParameters(
        AssignedConnector(Notations.f, LambdaConnector(x => x)),
        AssignedPredicate(Notations.a, formula"forall z. (z in U({})) <=> (z in {})")
      )
    ))

    focus(1)
    val _ = thmExtSchema(AssignedFunction(Notations.s, unionSet(emptySet)))(AssignedFunction(Notations.t, emptySet)).display()
    apply(justification) // Uses the previously proved theorem

    apply(introRForallS(RuleParameters(AssignedFunction(Notations.t, s))))

    apply(RuleSubstituteRightIff(
      RuleParameters()
        .withConnector(Notations.f, x => x <=> (s in emptySet))
        .withPredicate(Notations.a, formula"exists y. (?s in y) /\ (y in {})")
    ))

    focus(1)
    val _ = thmUnionSchema(AssignedFunction(t, emptySet)).rewrite(state.goals.head).display()
    apply(justification)

    apply(introRIff)
    apply(introRImp)
    apply(introLExists(RuleParameters(x -> y)))
    apply(introLAnd)
    apply(weaken(left = Set(0), right = Set(0)))
    apply(elimRNot)
    val _ = thmEmptySchema(AssignedFunction(s, me.cassayre.florian.masterproject.front.fol.FOL.VariableTerm(y))).display()
    apply(justification)

    apply(introRImp)
    apply(weaken(right = Set(0)))
    apply(elimRNot)
    apply(justification)

    asTheorem() // |- U({}) = {}
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thmUnionEmpty)))

  val lemmaSubsetRefl = {
    val p = ProofMode(sequent"|- (?s sub ?s) <=> ((?t in ?s) => (?t in ?s))")
    import p.*

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, x => formula"$x <=> ((?t in ?s) => (?t in ?s))")
        .withPredicate(Notations.a, formula"forall z. (z in ?s) => (z in ?s)")
    ))
    focus(1)
    apply(rewrite(sequent"|- (?s sub ?s) <=> (forall z. (z in ?s) => (z in ?s))"))
    val _ = thmSubsetSchema(AssignedFunction(t, s)).display()
    apply(justification)
    apply(introRIff)
    apply(introRImp)
    apply(introLForall(RuleParameters(AssignedFunction(Notations.t, t))))
    apply(introHypo)
    apply(introRImp)
    apply(weaken(left = Set(0)))
    apply(introRForallS(RuleParameters(AssignedFunction(Notations.t, v))))
    apply(solveProp)

    asTheorem()
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(lemmaSubsetRefl)))

  val thmUnionAny = {
    val p = ProofMode(() |- unionSet(powerSet(s)) === s)
    import p.*

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"forall z. (z in U(P(?s))) <=> (z in ?s)")
    ))
    focus(1)

    val _ = thmExtSchema(AssignedFunction(Notations.t, unionSet(powerSet(s))))(AssignedFunction(Notations.u, s))
      .rewrite(sequent"|- (forall z. (z in U(P(?s))) <=> (z in ?s)) <=> (U(P(?s)) = ?s)")
      .display()
    apply(justification)

    apply(introRForallS(RuleParameters(AssignedFunction(Notations.t, t))))


    apply(RuleSubstituteRightIff(
      RuleParameters()
        .withConnector(Notations.f, x => formula"(?t in U(P(?s))) <=> $x")
        .withPredicate(Notations.a, formula"exists y. (?t in y) /\ (y in P(?s))")
    ))

    // TODO: avoid using a temporary variable here
    val _ = thmUnionSchema(AssignedFunction(s, u))(AssignedFunction(t, powerSet(s)))(AssignedFunction(u, t)).display()
    apply(justification)

    apply(introRIff)
    apply(introRImp)
    apply(introLExistsS(RuleParameters(AssignedFunction(Notations.t, u))))
    apply(introLAnd)

    apply(elimLSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"?u sub ?s")
        .withPredicate(Notations.b, formula"?u in P(?s)")
    ))
    focus(1)
    apply(weaken(left = Set(0), right = Set(0)))
    apply(rewrite(sequent"|- (?u in P(?s)) <=> (?u sub ?s)"))
    val _ = thmPowerSchema(AssignedFunction(s, u))(AssignedFunction(t, s)).display()
    apply(justification)

    apply(elimLSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"forall z. (z in ?u) => (z in ?s)")
        .withPredicate(Notations.b, formula"?u sub ?s")
    ))
    focus(1)
    apply(weaken(left = Set(0), right = Set(0)))
    apply(rewrite(sequent"|- (?u sub ?s) <=> (forall z. (z in ?u) => (z in ?s))"))
    val _ = thmSubsetSchema(AssignedFunction(s, u))(AssignedFunction(t, s)).display()
    apply(justification)

    apply(introLForall(RuleParameters(AssignedFunction(Notations.t, t))))
    apply(solveProp)

    apply(introRExists(RuleParameters(AssignedFunction(Notations.t, s))))
    apply(solveProp)

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"?s sub ?s")
    ))
    focus(1)
    apply(weaken(left = Set(0)))
    apply(rewrite(sequent"|- (?s in P(?s)) <=> (?s sub ?s)"))
    val _ = thmPowerSchema(AssignedFunction(t, s)).display()
    apply(justification)

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"(?t in ?s) => (?t in ?s)")
    ))
    focus(1)
    apply(weaken(left = Set(0)))
    apply(rewrite(sequent"|- (?s sub ?s) <=> ((?t in ?s) => (?t in ?s))"))
    lemmaSubsetRefl.display()
    apply(justification)
    apply(solveProp)

    asTheorem()
  }

  println(Printer.prettySCProof(reconstructSCProofForTheorem(thmUnionAny)))

}
