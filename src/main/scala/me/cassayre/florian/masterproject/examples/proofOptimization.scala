package me.cassayre.florian.masterproject.examples

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.{SCProof, SCProofChecker}
import me.cassayre.florian.masterproject.front.printer.KernelPrinter
import me.cassayre.florian.masterproject.util.SCUtils

@main def proofOptimization(): Unit = {

  val (la, lb, lc) = (SchematicPredicateLabel("a", 0), SchematicPredicateLabel("b", 0), SchematicPredicateLabel("c", 0))
  val (a, b, c) = (PredicateFormula(la, Seq.empty), PredicateFormula(lb, Seq.empty), PredicateFormula(lc, Seq.empty))

  def printSeparator(): Unit = println("=================")

  def testProofOptimization(proof: SCProof): Unit = {
    val originalChecked = SCProofChecker.checkSCProof(proof)
    println("Original proof:")
    println(KernelPrinter.prettyProof(proof, judgement = originalChecked))

    assert(originalChecked.isValid)

    val optimized = SCUtils.optimizeProofIteratively(proof)
    val optimizedChecked = SCProofChecker.checkSCProof(optimized)
    println()
    println("Simplified proof:")
    println(KernelPrinter.prettyProof(optimized, judgement = optimizedChecked))

    assert(proof.conclusion == optimized.conclusion) // The conclusion must remain the same
    assert(optimizedChecked.isValid) // The proof must still be valid

    def compare(criterion: String, f: SCProof => Any): Unit = {
      val (before, after) = (f(proof), f(optimized))
      val result = if(before != after) s"$before -> $after" else s"$before (unchanged)"
      println(s"$criterion:\t$result")
    }

    println()
    println("STATISTICS")
    compare("Size", SCUtils.proofSize)
    compare("Depth", SCUtils.proofDepth)

    printSeparator()
  }

  printSeparator()

  // Test cases

  testProofOptimization(SCProof(
    Hypothesis(a |- a, a),
    LeftAnd((a, a /\ a) |- a, 0, a, a),
    RightImplies((a /\ a) |- (a ==> a), 1, a, a),
  ))

  testProofOptimization(SCProof(
    Hypothesis(a |- a, a),
    Rewrite(a |- (a \/ a), 0),
    Rewrite(a |- (a \/ a, a), 1),
    Weakening((a, b) |- (a, c), 2),
    Rewrite((a, b) |- (a, a \/ c), 3),
  ))

  testProofOptimization(SCProof(
    Hypothesis(a |- a, a),
    SCSubproof(SCProof(
      IndexedSeq(
        SCSubproof(SCProof(
          IndexedSeq(
            RightOr(a |- (a \/ b), -1, a, b)
          ),
          IndexedSeq(a |- a)
        ), Seq(-1)),
        LeftAnd((a /\ c) |- (a \/ b), 0, a, c)
      ),
      IndexedSeq(a |- a)
    ), Seq(0)),
    RightImplies(() |- (a /\ c) ==> (a \/ b), 1, a /\ c, a \/ b),
  ))

}
