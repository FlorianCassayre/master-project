package me.cassayre.florian.masterproject.legacy

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.legacy.unification.Unifier.*
import org.scalatest.funsuite.AnyFunSuite

class UnificationTests extends AnyFunSuite {

  val (sa, sb, sc) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))

  val (a, b, c) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))

  def checkUnifies(pattern: Formula, target: Formula): Unit = {
    unify(pattern, target) match {
      case _: UnificationSuccess => () // OK
      case UnificationFailure(message) => throw AssertionError(s"Did not unify: $message")
    }
  }

  def checkDoesNotUnify(pattern: Formula, target: Formula): Unit = {
    unify(pattern, target) match {
      case _: UnificationSuccess => throw AssertionError(s"It did unify")
      case _: UnificationFailure => () // OK
    }
  }

  test("unification") {
    checkUnifies(sa, a)
    checkUnifies(sa /\ sb, (a \/ b) /\ (b ==> c))
    checkUnifies(sa /\ sa, b /\ b)
    checkUnifies(sa /\ b, sb /\ b)

    checkDoesNotUnify(sa /\ sa, a /\ b)
  }

}
