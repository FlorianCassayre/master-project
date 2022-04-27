package me.cassayre.florian.masterproject.front

import me.cassayre.florian.masterproject.front.{*, given}
import org.scalatest.funsuite.AnyFunSuite

class Unification2Tests extends AnyFunSuite {

  val (sa, sb, sc) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  def unify(pattern: Formula, target: Formula): Boolean = {
    unifyAndResolve(
      IndexedSeq(PartialSequent(IndexedSeq(pattern), IndexedSeq.empty)),
      IndexedSeq(Sequent(IndexedSeq(target), IndexedSeq.empty)),
      IndexedSeq.empty,
      UnificationContext(),
      IndexedSeq((IndexedSeq(0), IndexedSeq.empty))
    ).nonEmpty
  }

  def checkUnifies(pattern: Formula, target: Formula): Unit = {
    assert(unify(pattern, target), "Did not unify")
  }

  def checkDoesNotUnify(pattern: Formula, target: Formula): Unit = {
    assert(!unify(pattern, target), "It did unify")
  }

  test("unification 2") {
    checkUnifies(a, a)
    checkDoesNotUnify(a, b)
    checkDoesNotUnify(a, sa)
    checkUnifies(a /\ b, a /\ b)
    checkUnifies(sa, a)
    checkUnifies(sa, sa)
    checkUnifies(sa /\ b, a /\ b)
    checkUnifies(sa /\ sb, a /\ b)
    checkUnifies(sa /\ b, sb /\ b)
    checkUnifies(sa /\ sb, (a ==> b) /\ (c \/ a))
    checkUnifies(sa /\ sa, b /\ b)
    checkDoesNotUnify(sa /\ sa, a /\ b)
  }

}
