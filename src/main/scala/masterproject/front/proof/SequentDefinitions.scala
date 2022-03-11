package masterproject.front.proof

import lisa.kernel.Printer
import masterproject.front.fol.FOL.*

trait SequentDefinitions {

  sealed abstract class SequentBase {
    val left: IndexedSeq[Formula]
    val right: IndexedSeq[Formula]

    def formulas: IndexedSeq[Formula] = left ++ right
  }

  // TODO this should be handled by its own printer
  private def prettySequent(left: Seq[Formula], right: Seq[Formula], partial: Boolean = false): String = {
    def prettySequence(seq: Seq[Formula], leftSide: Boolean): String = {
      val strs = seq.map(Printer.prettyFormula(_))
      val rest = "..."
      val strs1 = if(partial) if(leftSide) rest +: strs else strs :+ rest else strs
      strs1.mkString("; ")
    }

    s"${prettySequence(left, true)} ⊢ ${prettySequence(right, false)}"
  }

  final case class Sequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) extends SequentBase {
    override def toString: String = prettySequent(left, right)
  }
  final case class PartialSequent(left: IndexedSeq[Formula], right: IndexedSeq[Formula]) extends SequentBase {
    override def toString: String = prettySequent(left, right, partial = true)
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

}
