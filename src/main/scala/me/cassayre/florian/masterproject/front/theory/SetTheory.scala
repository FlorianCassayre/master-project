package me.cassayre.florian.masterproject.front.theory

import lisa.kernel.proof.RunningTheory
import lisa.settheory.AxiomaticSetTheory
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*

object SetTheory {

  // The purpose of this file is simply to lift the definitions from the kernel to the front

  opaque type AxiomaticFormula <: Formula = Formula

  def newSetTheoryEnvironment(): ProofEnvironment = {
    val runningTheory = new RunningTheory()
    AxiomaticSetTheory.functions.foreach(runningTheory.addSymbol)
    AxiomaticSetTheory.predicates.foreach(runningTheory.addSymbol)
    AxiomaticSetTheory.axioms.foreach(runningTheory.addAxiom)
    new ProofEnvironment(runningTheory)
  }

  val membership: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.in).asInstanceOf[ConstantPredicateLabel[2]]
  val subset: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.subset).asInstanceOf[ConstantPredicateLabel[2]]
  val sameCardinality: ConstantPredicateLabel[2] = fromKernel(AxiomaticSetTheory.in).asInstanceOf[ConstantPredicateLabel[2]]

  val emptySet: ConstantFunctionLabel[0] = fromKernel(AxiomaticSetTheory.emptySet).asInstanceOf[ConstantFunctionLabel[0]]
  val unorderedPairSet: ConstantFunctionLabel[2] = fromKernel(AxiomaticSetTheory.pair).asInstanceOf[ConstantFunctionLabel[2]]
  val singletonSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.singleton).asInstanceOf[ConstantFunctionLabel[1]]
  val powerSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.powerSet).asInstanceOf[ConstantFunctionLabel[1]]
  val unionSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.union).asInstanceOf[ConstantFunctionLabel[1]]
  val universeSet: ConstantFunctionLabel[1] = fromKernel(AxiomaticSetTheory.universe).asInstanceOf[ConstantFunctionLabel[1]]

  val axiomEmpty: AxiomaticFormula = fromKernel(AxiomaticSetTheory.emptySetAxiom)
  val axiomExtensionality: AxiomaticFormula = fromKernel(AxiomaticSetTheory.extensionalityAxiom)
  val axiomPair: AxiomaticFormula = fromKernel(AxiomaticSetTheory.pairAxiom)
  val axiomUnion: AxiomaticFormula = fromKernel(AxiomaticSetTheory.unionAxiom)
  val axiomPower: AxiomaticFormula = fromKernel(AxiomaticSetTheory.powerAxiom)
  val axiomFoundation: AxiomaticFormula = fromKernel(AxiomaticSetTheory.foundationAxiom)

  val axiomSchemaReplacement: AxiomaticFormula = fromKernel(AxiomaticSetTheory.replacementSchema)

  val axiomTarski: AxiomaticFormula = fromKernel(AxiomaticSetTheory.tarskiAxiom)

  extension (term: Term) {
    def in(other: Term): Formula = membership(term, other)
    def subsetOf(other: Term): Formula = subset(term, other)
    def ~(other: Term): Formula = sameCardinality(term, other)
  }

  extension (formula: AxiomaticFormula) {
    def asJustified(using env: ProofEnvironment): Axiom = env.mkAxiom(formula)
  }

}
