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
  val (s, t, u) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"), SchematicFunctionLabel[0]("u"))
  val (x, y, z) = (VariableLabel("x"), me.cassayre.florian.masterproject.front.fol.FOL.VariableLabel("y"), VariableLabel("z"))

  given ProofEnvironment = newSetTheoryEnvironment()

  val axExt: Axiom = axiomExtensionality.asJustified.display()
  val axEmpty: Axiom = axiomEmpty.asJustified.display()
  val axUnion: Axiom = axiomUnion.asJustified.display()

  // 1. Generalize universal quantifiers

  val thmExtSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axExt).get
    val t1 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, t)))(t0).get
    t1
  }.display()

  val thmEmptySchema: Theorem = elimRForallS(
    RuleParameters(AssignedPredicate(Notations.p, LambdaPredicate(x => !(x in emptySet))), AssignedFunction(Notations.t, s))
  )(axEmpty).get.display()

  val thmUnionSchema: Theorem = {
    val t0 = elimRForallS(RuleParameters(AssignedFunction(Notations.t, s)))(axUnion).get
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
    val _ = thmUnionSchema(AssignedFunction(t, emptySet)).rewrite(state.goals.head).get.display()
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
}
