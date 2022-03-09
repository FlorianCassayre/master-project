package masterproject.front.fol.definitions

trait FormulaDefinitions extends FormulaLabelDefinitions with TermDefinitions {

  sealed abstract class Formula extends TreeWithLabel[FormulaLabel] {
    def predicates: Set[PredicateLabel[?]]
  }

  final case class PredicateFormula[N <: Arity] protected(label: PredicateLabel[N], args: Seq[Term]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.flatMap(_.freeVariables).toSet
    override def predicates: Set[PredicateLabel[?]] = Set(label)
    override def functions: Set[FunctionLabel[?]] = args.flatMap(_.functions).toSet
  }
  object PredicateFormula {
    def unsafe(label: PredicateLabel[?], args: Seq[Term]): PredicateFormula[?] = PredicateFormula(label, args)
  }

  final case class ConnectorFormula[N <: Arity] protected(label: ConnectorLabel[N], args: Seq[Formula]) extends Formula {
    override def freeVariables: Set[VariableLabel] = args.flatMap(_.freeVariables).toSet
    override def predicates: Set[PredicateLabel[?]] = args.flatMap(_.predicates).toSet
    override def functions: Set[FunctionLabel[?]] = args.flatMap(_.functions).toSet
  }
  object ConnectorFormula {
    def unsafe(label: ConnectorLabel[?], args: Seq[Formula]): ConnectorFormula[?] = ConnectorFormula(label, args)
  }

  final case class BinderFormula(label: BinderLabel, bound: VariableLabel, inner: Formula) extends Formula {
    override def freeVariables: Set[VariableLabel] = inner.freeVariables - bound
    override def predicates: Set[PredicateLabel[?]] = inner.predicates
    override def functions: Set[FunctionLabel[?]] = inner.functions
  }
  
}
