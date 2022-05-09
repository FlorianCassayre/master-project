package me.cassayre.florian.masterproject.front

import scala.language.adhocExtensions

import org.scalatest.funsuite.AnyFunSuite
import me.cassayre.florian.masterproject.front.{*, given}

class FrontMacroTests extends AnyFunSuite {

  test("string interpolation macros") {
    term"g(x, y)"
    formula"a /\ b \/ c => d"
    sequent"a; b |- c"
    partial"a |- b; ..."

    val p = ConstantPredicateLabel[2]("p")
    assert(formula"$p(x, y)".toString == "p(x, y)")

    val f = SchematicFunctionLabel[2]("f")
    val y0 = SchematicFunctionLabel[0]("y")()
    assert(term"{$f(x, $y0)}".toString == "{?f(x, ?y)}")
    assert(formula"{} = {$f(x, $y0)}".toString == "∅ = {?f(x, ?y)}")

    val p0 = ConstantPredicateLabel[0]("p")
    val v = VariableLabel("x")
    assert(sequent" |-  $p0".toString == "⊢ p")
    assert(partial"\ $v. $v = {}; f($y0)  |- $p0 /\ b; ...".toString == raw"\x. f(?y); x = ∅ ⊢ p ∧ b; …")
  }

}
