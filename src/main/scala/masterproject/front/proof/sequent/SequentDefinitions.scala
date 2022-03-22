package masterproject.front.proof.sequent

import lisa.kernel.Printer
import masterproject.front.fol.FOL.*

trait SequentDefinitions {

  sealed abstract class SequentBase {
    val left: IndexedSeq[Formula]
    val right: IndexedSeq[Formula]

    def formulas: IndexedSeq[Formula] = left ++ right
  }

  // TODO this should be handled by its own printer
  private def prettySequent(left: Seq[Formula], right: Seq[Formula], partialLeft: Boolean = false, partialRight: Boolean = false): String = {
    def prettySequence(seq: Seq[Formula], leftSide: Boolean, partial: Boolean): String = {
      val strs = seq.map(Printer.prettyFormula(_))
      val rest = "..."
      val strs1 = if (partial) if (leftSide) rest +: strs else strs :+ rest else strs
      strs1.mkString("; ")
    }

    s"${prettySequence(left, true, partialLeft)} ⊢ ${prettySequence(right, false, partialRight)}"
  }

  final case class Sequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) extends SequentBase {
    override def toString: String = prettySequent(left, right)
  }

  final case class PartialSequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula], partialLeft: Boolean = true, partialRight: Boolean = true) extends SequentBase {
    override def toString: String = prettySequent(left, right, partialLeft, partialRight)
  }

  def functionsOfSequent(sequent: SequentBase): Set[FunctionLabel[?]] = sequent.formulas.flatMap(functionsOf).toSet

  def predicatesOfSequent(sequent: SequentBase): Set[PredicateLabel[?]] = sequent.formulas.flatMap(predicatesOf).toSet

  def schematicFunctionsOfSequent(sequent: SequentBase): Set[SchematicFunctionLabel[?]] =
    functionsOfSequent(sequent).collect { case l: SchematicFunctionLabel[?] => l }

  def schematicPredicatesOfSequent(sequent: SequentBase): Set[SchematicPredicateLabel[?]] =
    predicatesOfSequent(sequent).collect { case l: SchematicPredicateLabel[?] => l }

  def schematicConnectorsOfSequent(sequent: SequentBase): Set[SchematicConnectorLabel[?]] =
    sequent.formulas.flatMap(schematicConnectorsOf).toSet

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

}
