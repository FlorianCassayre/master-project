package masterproject.front

import masterproject.front.proof.Proof.*
import masterproject.front.fol.FOL.*

@main def tests3(): Unit = {
  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  val (w, x, y, z) = (SchematicPredicateLabel[0]("w"), SchematicPredicateLabel[0]("x"), SchematicPredicateLabel[0]("y"), SchematicPredicateLabel[0]("z"))

  val ctx = new ProofEnvironment
  given ProofEnvironment = ctx

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

  val thmAandBComm = thmAndComm(x, a())(y, b())

  println(thmAandBComm)

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

}
