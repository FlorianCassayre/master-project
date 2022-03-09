package masterproject.front.fol.definitions

trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  sealed abstract class Formula extends TreeWithLabel[FormulaLabel]

  final case class PredicateFormula[N <: Arity] protected(label: PredicateLabel[N], args: Seq[Term]) extends Formula
  object PredicateFormula {
    def unsafe(label: PredicateLabel[?], args: Seq[Term]): PredicateFormula[?] = PredicateFormula(label, args)
  }

  final case class ConnectorFormula[N <: Arity] protected(label: ConnectorLabel[N], args: Seq[Formula]) extends Formula
  object ConnectorFormula {
    def unsafe(label: ConnectorLabel[?], args: Seq[Formula]): ConnectorFormula[?] = ConnectorFormula(label, args)
  }

  final case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula
  
}
