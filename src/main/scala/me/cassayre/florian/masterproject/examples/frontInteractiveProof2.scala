package me.cassayre.florian.masterproject.examples

import me.cassayre.florian.masterproject.front.fol.FOL.{*, given}
import me.cassayre.florian.masterproject.front.parser.FrontMacro.{*, given}
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter.*
import me.cassayre.florian.masterproject.front.printer.{FrontPrintStyle, KernelPrinter}
import me.cassayre.florian.masterproject.front.proof.Proof.{*, given}
import me.cassayre.florian.masterproject.front.theory.SetTheory.*

import scala.util.chaining.*

@main def frontInteractiveProof2(): Unit = {
  val (s, t, u, v) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"), SchematicFunctionLabel[0]("v"))

  given ProofEnvironment = newSetTheoryEnvironment()

  val axExt: Axiom = axiomExtensionality.asJustified.display()
  val axUnion: Axiom = axiomUnion.asJustified.display()
  val axPower: Axiom = axiomPower.asJustified.display()
  val defSubset: Axiom = definitionSubset.asJustified.display()

  // 1. Generalize universal quantifiers

  val thmExtSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axExt).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

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

  // 2. Prove a lemma

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
    apply(justificationInst(thmSubsetSchema))
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

  // 3. Prove the complete theorem

  val thmUnionAny = {
    val p = ProofMode(() |- unionSet(powerSet(s)) === s)
    import p.*

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"forall z. (z in U(P(?s))) <=> (z in ?s)")
    ))
    focus(1)

    apply(justification(
      thmExtSchema(AssignedFunction(Notations.t, unionSet(powerSet(s))))(AssignedFunction(Notations.u, s))
        .rewrite(sequent"|- (forall z. (z in U(P(?s))) <=> (z in ?s)) <=> (U(P(?s)) = ?s)")
        .display()
    ))

    apply(introRForallS(RuleParameters(AssignedFunction(Notations.t, t))))


    apply(RuleSubstituteRightIff(
      RuleParameters()
        .withConnector(Notations.f, x => formula"(?t in U(P(?s))) <=> $x")
        .withPredicate(Notations.a, formula"exists y. (?t in y) /\ (y in P(?s))")
    ))

    apply(justificationInst(thmUnionSchema))

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
    apply(justificationInst(thmPowerSchema))

    apply(elimLSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"forall z. (z in ?u) => (z in ?s)")
        .withPredicate(Notations.b, formula"?u sub ?s")
    ))
    focus(1)
    apply(weaken(left = Set(0), right = Set(0)))
    apply(rewrite(sequent"|- (?u sub ?s) <=> (forall z. (z in ?u) => (z in ?s))"))
    apply(justificationInst(thmSubsetSchema))

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
    apply(justificationInst(thmPowerSchema))

    apply(elimRSubstIff(
      RuleParameters()
        .withConnector(Notations.f, identity)
        .withPredicate(Notations.a, formula"(?t in ?s) => (?t in ?s)")
    ))
    focus(1)
    apply(weaken(left = Set(0)))
    apply(rewrite(sequent"|- (?s sub ?s) <=> ((?t in ?s) => (?t in ?s))"))
    apply(justification(lemmaSubsetRefl))
    apply(solveProp)

    asTheorem()
  }
}
