package me.cassayre.florian.masterproject.front.fol.definitions

trait TermDefinitions extends TermLabelDefinitions {

  protected def pretty(term: Term): String

  sealed abstract class Term extends LabeledTree[TermLabel] {
    override def toString: String = pretty(this)
  }

  final case class VariableTerm(label: VariableLabel) extends Term

  final case class FunctionTerm protected(label: FunctionLabel[?], args: Seq[Term]) extends Term {
    require(label.arity == -1 || label.arity == args.size)
    val arity: Int = label.arity
  }
  object FunctionTerm {
    def unsafe(label: FunctionLabel[?], args: Seq[Term]): FunctionTerm = FunctionTerm(label, args)
  }

}
