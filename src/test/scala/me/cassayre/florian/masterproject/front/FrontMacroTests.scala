package me.cassayre.florian.masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.front.*

class FrontMacroTests extends AnyFunSuite {

  test("string interpolation macros") {
    term"g(x, y)"
    formula"a /\ b \/ c => d"
    sequent"a; b |- c"
    partial"a |- b; ..."

    val p = ConstantPredicateLabel("p", 2)
    assert(formula"$p(x, y)".toString == s"p(x, y)") // Currently limited support for label interpolation, very few safety guarantees
  }

}
