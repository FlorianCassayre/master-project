package masterproject.front

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import masterproject.front.Unification.*
import org.scalatest.funsuite.AnyFunSuite

class UnificationTests extends AnyFunSuite {

  val (lsa, lsb, lsc) = (SchematicPredicateLabel("a", 0), SchematicPredicateLabel("b", 0), SchematicPredicateLabel("c", 0))
  val (sa, sb, sc) = (PredicateFormula(lsa, Seq.empty), PredicateFormula(lsb, Seq.empty), PredicateFormula(lsc, Seq.empty))

  val (la, lb, lc) = (ConstantPredicateLabel("a", 0), ConstantPredicateLabel("b", 0), ConstantPredicateLabel("c", 0))
  val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))

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
