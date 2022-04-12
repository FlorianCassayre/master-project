package me.cassayre.florian.masterproject.front

import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.front.*

class FrontMacroTests extends AnyFunSuite {

  test("string interpolation macros") {
    term"g(x, y)"
    formula"a /\ b \/ c => d"
    sequent"a; b |- c"
    partial"a |- b; ..."
  }

}
