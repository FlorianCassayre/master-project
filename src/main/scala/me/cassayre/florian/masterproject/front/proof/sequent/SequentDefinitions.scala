package me.cassayre.florian.masterproject.front.proof.sequent

import lisa.kernel.Printer
import me.cassayre.florian.masterproject.front.fol.FOL.*

trait SequentDefinitions {

  protected def pretty(sequent: Sequent): String
  protected def pretty(sequent: PartialSequent): String

  sealed abstract class SequentBase {
    val left: IndexedSeq[Formula]
    val right: IndexedSeq[Formula]

    def formulas: IndexedSeq[Formula] = left ++ right
  }

  final case class Sequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) extends SequentBase {
    override def toString: String = pretty(this)
  }

  final case class PartialSequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula], partialLeft: Boolean = true, partialRight: Boolean = true) extends SequentBase {
    override def toString: String = pretty(this)
  }

  def functionsOfSequent(sequent: SequentBase): Set[FunctionLabel[?]] = sequent.formulas.flatMap(functionsOf).toSet

  def predicatesOfSequent(sequent: SequentBase): Set[PredicateLabel[?]] = sequent.formulas.flatMap(predicatesOf).toSet

  def schematicFunctionsOfSequent(sequent: SequentBase): Set[SchematicFunctionLabel[?]] =
    functionsOfSequent(sequent).collect { case l: SchematicFunctionLabel[?] => l }

  def schematicPredicatesOfSequent(sequent: SequentBase): Set[SchematicPredicateLabel[?]] =
    predicatesOfSequent(sequent).collect { case l: SchematicPredicateLabel[?] => l }

  def schematicConnectorsOfSequent(sequent: SequentBase): Set[SchematicConnectorLabel[?]] =
    sequent.formulas.flatMap(schematicConnectorsOf).toSet

  def freeVariablesOfSequent(sequent: SequentBase): Set[VariableLabel] = sequent.formulas.flatMap(freeVariablesOf).toSet

  def declaredBoundVariablesOfSequent(sequent: SequentBase): Set[VariableLabel] =
    sequent.formulas.flatMap(declaredBoundVariablesOf).toSet

  def isSequentWellFormed(sequent: SequentBase): Boolean =
    sequent.formulas.forall(isWellFormed)

  // Only full sequents should be converted to the kernel
  def sequentToKernel(sequent: Sequent): lisa.kernel.proof.SequentCalculus.Sequent =
    lisa.kernel.proof.SequentCalculus.Sequent(
      sequent.left.map(toKernel).toSet,
      sequent.right.map(toKernel).toSet
    )

  given Conversion[Sequent, lisa.kernel.proof.SequentCalculus.Sequent] = sequentToKernel

  def isSameSequent(s1: Sequent, s2: Sequent): Boolean =
    lisa.kernel.proof.SequentCalculus.isSameSequent(s1, s2)

  def instantiateSequentSchemas(
    sequent: Sequent,
    functions: Seq[AssignedFunction] = Seq.empty,
    predicates: Seq[AssignedPredicate] = Seq.empty,
    connectors: Seq[AssignedConnector] = Seq.empty,
  ): Sequent = {
    def instantiate(formulas: IndexedSeq[Formula]): IndexedSeq[Formula] =
      formulas.map(instantiateFormulaSchemas(_, functions, predicates, connectors))
    Sequent(instantiate(sequent.left), instantiate(sequent.right))
  }

}
