package me.cassayre.florian.masterproject.parser

import lisa.kernel.Printer
import lisa.kernel.proof.SCProofChecker
import org.scalatest.funsuite.AnyFunSuite

import scala.util.Try

class SCReaderTests extends AnyFunSuite {

  test("parser positive examples (ASCII)") {
    Seq[String](
      "|- a",
      "a |- b",
      """(a /\ b => ((c <=> d))) |- exists x. f(x)""",
      "forall x,y    , z.exists  w . f(g(w), (x),y)|-a",
      "|- {}={x, {{},y}}",
      "|- Subproof",
      "\\y. f(y) |- \\x. g(x)"
    ).foreach(s => SCReader.readSequentAscii(s))
  }

  test("parser negative examples (ASCII)") {
    Seq[String](
      "",
      "|--",
      "a",
      "a |- b |- c",
      "|- w = {x,y,z}",
      "|- a b",
      "|- (x = y"
    ).foreach(s => Try(SCReader.readSequentAscii(s)).isFailure)
  }

  test("parser proof") {
    Seq(
      """
        |-1 Import 0   ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 0 Rewrite -1 ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 1 Hypo.      \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 2 Left ∀ 1   ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 3 Cut 0, 2   ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 4 Hypo.      \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 5 Left ∀ 4   \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 6 Cut 3, 5   ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 7 Hypo.      \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 8 Left ∀ 7   \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 9 Cut 6, 8   ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |""".stripMargin,
      """
        |-1        Import 0    ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 0        Rewrite -1  ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 1        Subproof -1 ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |   -1     Import 0    ⊢ ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |    0     Subproof    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |      0   Subproof    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |        0 Hypo.       \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |        1 Left ∀ 0    ∀x, y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |    1     Cut -1, 0   ⊢ \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 2        Hypo.       \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 3        Left ∀ 2    \x. ∀y, z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 4        Cut 1, 3    ⊢ \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 5        Hypo.       \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 6        Left ∀ 5    \x, y. ∀z. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z) ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        | 7        Cut 4, 6    ⊢ \z, x, y. (z ∈ {x, y}) ↔ (x = z) ∨ (y = z)
        |""".stripMargin,
    ).foreach { input =>
      val proof = SCReader.readProof(input)
      println(Printer.prettySCProof(proof))
      println()
      assert(SCProofChecker.checkSCProof(proof).isValid)
      //assert(Printer.prettySCProof(proof) == input.trim) // TODO uncomment this when the printer is updated
    }
  }

}
