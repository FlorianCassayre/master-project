package me.cassayre.florian.masterproject.front.fol.definitions

trait TermDefinitions extends TermLabelDefinitions {

  protected def pretty(term: Term): String

  /** @see [[lisa.kernel.fol.FOL.Term]] */
  sealed abstract class Term extends LabeledTree[TermLabel] {
    override def toString: String = pretty(this)
  }

  /** @see [[lisa.kernel.fol.FOL.VariableTerm]] */
  final case class VariableTerm(label: VariableLabel) extends Term

  /** @see [[lisa.kernel.fol.FOL.FunctionTerm]] */
  final case class FunctionTerm protected(label: FunctionLabel[?], args: Seq[Term]) extends Term {
    require(isLegalApplication(label, args))
  }
  object FunctionTerm {
    def unsafe(label: FunctionLabel[?], args: Seq[Term]): FunctionTerm = FunctionTerm(label, args)
  }

}
