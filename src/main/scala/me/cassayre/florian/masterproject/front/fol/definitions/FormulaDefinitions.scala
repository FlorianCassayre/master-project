package me.cassayre.florian.masterproject.front.fol.definitions

trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {
  
  protected def pretty(formula: Formula): String

  sealed abstract class Formula extends LabeledTree[FormulaLabel] {
    override def toString: String = pretty(this)
  }

  final case class PredicateFormula protected(label: PredicateLabel[?], args: Seq[Term]) extends Formula
  object PredicateFormula {
    def unsafe(label: PredicateLabel[?], args: Seq[Term]): PredicateFormula = PredicateFormula(label, args)
  }

  final case class ConnectorFormula protected(label: ConnectorLabel[?], args: Seq[Formula]) extends Formula
  object ConnectorFormula {
    def unsafe(label: ConnectorLabel[?], args: Seq[Formula]): ConnectorFormula = ConnectorFormula(label, args)
  }

  final case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula

}
