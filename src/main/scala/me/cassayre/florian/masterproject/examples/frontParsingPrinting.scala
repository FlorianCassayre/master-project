package me.cassayre.florian.masterproject.examples

import me.cassayre.florian.masterproject.front.*
import me.cassayre.florian.masterproject.front.fol.FOL
import me.cassayre.florian.masterproject.front.parser.{FrontReader, KernelReader}
import me.cassayre.florian.masterproject.front.printer.{FrontPositionedPrinter, KernelPrinter}
import me.cassayre.florian.masterproject.legacy.parser.ReadingException.ParsingException

import scala.util.{Failure, Success, Try}

@main def frontParsingPrinting(): Unit = {

  val a = FOL.SchematicPredicateLabel[0]("a")
  val p = FOL.SchematicPredicateLabel[1]("p")
  val t = FOL.SchematicFunctionLabel[0]("t")

  // The lines that are commented do not compile (and are, in fact, incorrect)
  Seq[Term | Formula | Sequent | PartialSequent](
    sequent"|- ?a",
    sequent"?a; ?b |- ?c",
    sequent"|- forall x. !(x in {})",
    sequent"|- forall x, y. (forall z. (z in x) <=> (z in y)) <=> (x = y)",
    sequent"|- $a",
    sequent"|- $p($t)",
    //sequent"|- $p($a)", // <- "expected term, got formula"
    sequent"|- ${p(t)}",
    //sequent"|- $p($t, $t)", // <- "arity mismatch: variable label expects 1 arguments but you provided 2"
    formula"?a /\ ?b",
    term"{?s, {f(?t), {}}}",
    partial"... |- ?a; ...",
  ).map {
    // The printer outputs a normal form
    case term: Term => FrontPositionedPrinter.prettyTerm(term)
    case formula: Formula => FrontPositionedPrinter.prettyFormula(formula)
    case sequent: Sequent => FrontPositionedPrinter.prettySequent(sequent)
    case partial: PartialSequent => FrontPositionedPrinter.prettyPartialSequent(partial)
  }.foreach(println)

  // The parsing can of course also be performed at runtime:
  FrontReader.readSequent("|- ?a"): Sequent

  // Parsing errors are designed to be user-friendly
  (Try(FrontReader.readSequent(raw"|- ?a /\ {}")): @unchecked) match {
    case Failure(e) => println(e)
    /*
    [1.10] failure: Type error: expected formula, got term

    |- ?a /\ {}
             ^
     */
  }

  // It is compatible with the kernel and supports proofs as well
  val proofStr = """
    |0    Hypo.        ?a ⊢ ?a; ?b            [?a]
    |1    Subproof 0   ⊢ ¬?a ∨ ?b → ?a → ?b
    |  -1 Import       ?a ⊢ ?a; ?b
    |   0 Left ¬ -1    ?a; ¬?a ⊢ ?b           [?a]
    |   1 Hypo.        ?a; ?b ⊢ ?b            [?b]
    |   2 Left ∨ 0, 1  ?a; ¬?a ∨ ?b ⊢ ?b      [¬?a; ?b]
    |   3 Right → 2    ¬?a ∨ ?b ⊢ ?a → ?b     [?a; ?b]
    |   4 Right → 3    ⊢ ¬?a ∨ ?b → ?a → ?b   [¬?a ∨ ?b; ?a → ?b]
    |2    Subproof 0   ⊢ (?a → ?b) → ¬?a ∨ ?b
    |  -1 Import       ?a ⊢ ?a; ?b
    |   0 Right ¬ -1   ⊢ ?a; ?b; ¬?a          [?a]
    |   1 Hypo.        ?b ⊢ ?b; ¬?a           [?b]
    |   2 Left → 0, 1  ?a → ?b ⊢ ?b; ¬?a      [?a; ?b]
    |   3 Right ∨ 2    ?a → ?b ⊢ ¬?a ∨ ?b     [¬?a; ?b]
    |   4 Right → 3    ⊢ (?a → ?b) → ¬?a ∨ ?b [?a → ?b; ¬?a ∨ ?b]
    |3    Right ↔ 1, 2 ⊢ ¬?a ∨ ?b ↔ ?a → ?b   [¬?a ∨ ?b; ?a → ?b]
  """.trim.stripMargin

  println(KernelPrinter.prettyProof(KernelReader.readProof(proofStr), explicit = true))

}
