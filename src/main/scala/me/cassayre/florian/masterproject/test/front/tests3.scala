package me.cassayre.florian.masterproject.test.front

import me.cassayre.florian.masterproject.front.{*, given}

@main def tests3(): Unit = {
  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))
  val s = SchematicFunctionLabel[0]("s")
  val v = VariableLabel("v")

  given ProofEnvironment = newEmptyEnvironment()

  val thmAndAssoc1 = {
    val p = ProofMode(a |- b ==> (a /\ b))

    p.apply(introRImp)
    p.apply(introRAnd)
    p.apply(introHypo)
    p.apply(introHypo)

    val thm = p.asTheorem()
  }
  val thmAndAssoc12 = {
    val t1 = introHypo(RuleParameters().withPredicate(Notations.a, a())).get
    val t2 = introHypo(RuleParameters().withPredicate(Notations.a, b())).get
    val t3 = introRAnd(t1, t2).get
    val thm = introRImp(t3).get
    println(thm)
  }
  val thmAndAssoc = {
    val proofMode = ProofMode(((x /\ y) /\ z) |- (x /\ (y /\ z)))
    import proofMode.*

    apply(introRAnd)
    apply(introLAnd)
    apply(introLAnd)
    apply(introHypo)
    apply(introRAnd)
    apply(introLAnd)
    apply(introLAnd)
    apply(introHypo)
    apply(introLAnd)
    apply(introHypo)

    asTheorem()
  }

  val thmAndComm = {
    val proofMode = ProofMode((x /\ y) |- (y /\ x))
    import proofMode.*

    apply(introRAnd)
    apply(introLAnd)
    apply(introHypo)
    apply(introLAnd)
    apply(introHypo)

    asTheorem()
  }

  val thmAandBComm = thmAndComm(AssignedPredicate(x, a()))(AssignedPredicate(y, b()))

  println(thmAandBComm)
  println()

  val thmOrAssoc = {
    val proofMode = ProofMode(((x \/ y) \/ z) |- (x \/ (y \/ z)))
    import proofMode.*

    apply(rewrite(right = Map(0 -> ((x \/ y) \/ z))))
    apply(introHypo)

    asTheorem()
  }

  val thmOrComm = {
    val proofMode = ProofMode((x \/ y) |- (y \/ x))
    import proofMode.*

    apply(introLOr)
    apply(solveProp)
    apply(solveProp)

    asTheorem()
  }

  thmOrComm.rewrite(((x \/ y) /\ z) |- ((y \/ x) /\ z)).display()

  val thmForallRefl = {
    val proofMode = ProofMode(() |- forall(v, v === v))
    import proofMode.*

    apply(RuleIntroductionRightForallSchema(
      RuleParameters()
        .withFunction(Notations.t, s())
    ))
    apply(introRRefl)

    asTheorem()
  }

}
