package masterproject.front.fol.conversions

import masterproject.front.fol.definitions.FormulaDefinitions

trait FormulaConversions extends TermConversions {
  this: FormulaDefinitions =>

  private val connectors: Map[ConstantConnectorLabel[?], lisa.kernel.fol.FOL.ConnectorLabel] = Map(
    neg -> lisa.kernel.fol.FOL.Neg,
    implies -> lisa.kernel.fol.FOL.Implies,
    iff -> lisa.kernel.fol.FOL.Iff,
    and -> lisa.kernel.fol.FOL.And,
    or -> lisa.kernel.fol.FOL.Or,
  )
  private val binders: Map[BinderLabel, lisa.kernel.fol.FOL.BinderLabel] = Map(
    forall -> lisa.kernel.fol.FOL.Forall,
    exists -> lisa.kernel.fol.FOL.Exists,
    existsOne -> lisa.kernel.fol.FOL.ExistsOne,
  )
  private val predicates: Map[ConstantPredicateLabel[?], lisa.kernel.fol.FOL.ConstantPredicateLabel] = Map(
    equality -> lisa.kernel.fol.FOL.equality.asInstanceOf[lisa.kernel.fol.FOL.ConstantPredicateLabel], // Sadly...
  )

  def toKernel(label: ConstantConnectorLabel[?]): lisa.kernel.fol.FOL.ConnectorLabel = connectors(label)

  def toKernel(label: ConnectorLabel[?]): lisa.kernel.fol.FOL.ConnectorLabel = label match {
    case constant: ConstantConnectorLabel[?] => toKernel(constant)
    case _: SchematicConnectorLabel[?] => throw new UnsupportedOperationException
  }

  def toKernel(label: ConstantPredicateLabel[?]): lisa.kernel.fol.FOL.ConstantPredicateLabel =
    predicates.getOrElse(label, lisa.kernel.fol.FOL.ConstantPredicateLabel(label.id, label.arity))

  def toKernel(label: SchematicPredicateLabel[?]): lisa.kernel.fol.FOL.SchematicPredicateLabel =
    lisa.kernel.fol.FOL.SchematicPredicateLabel(label.id, label.arity)

  def toKernel(label: PredicateLabel[?]): lisa.kernel.fol.FOL.PredicateLabel = label match {
    case constant: ConstantPredicateLabel[?] => toKernel(constant)
    case schematic: SchematicPredicateLabel[?] => toKernel(schematic)
  }

  def toKernel(label: BinderLabel): lisa.kernel.fol.FOL.BinderLabel = binders(label)

  def toKernel(label: FormulaLabel): lisa.kernel.fol.FOL.FormulaLabel = label match {
    case predicate: PredicateLabel[?] => toKernel(predicate)
    case connector: ConnectorLabel[?] => toKernel(connector)
    case binder: BinderLabel => toKernel(binder)
  }

  def toKernel(formula: PredicateFormula[?]): lisa.kernel.fol.FOL.PredicateFormula =
    lisa.kernel.fol.FOL.PredicateFormula(toKernel(formula.label), formula.args.map(toKernel))

  def toKernel(formula: ConnectorFormula[?]): lisa.kernel.fol.FOL.ConnectorFormula =
    lisa.kernel.fol.FOL.ConnectorFormula(toKernel(formula.label), formula.args.map(toKernel))

  def toKernel(formula: BinderFormula): lisa.kernel.fol.FOL.BinderFormula =
    lisa.kernel.fol.FOL.BinderFormula(toKernel(formula.label), toKernel(formula.bound), toKernel(formula.inner))

  def toKernel(formula: Formula): lisa.kernel.fol.FOL.Formula = formula match {
    case predicate: PredicateFormula[?] => toKernel(predicate)
    case connector: ConnectorFormula[?] => toKernel(connector)
    case binder: BinderFormula => toKernel(binder)
  }

  given Conversion[PredicateFormula[?], lisa.kernel.fol.FOL.PredicateFormula] = toKernel
  given Conversion[ConnectorFormula[?], lisa.kernel.fol.FOL.ConnectorFormula] = toKernel
  given Conversion[BinderFormula, lisa.kernel.fol.FOL.BinderFormula] = toKernel
  given Conversion[Formula, lisa.kernel.fol.FOL.Formula] = toKernel
  given Conversion[ConstantPredicateLabel[?], lisa.kernel.fol.FOL.ConstantPredicateLabel] = toKernel
  given Conversion[SchematicPredicateLabel[?], lisa.kernel.fol.FOL.SchematicPredicateLabel] = toKernel
  given Conversion[PredicateLabel[?], lisa.kernel.fol.FOL.PredicateLabel] = toKernel
  given Conversion[ConnectorLabel[?], lisa.kernel.fol.FOL.ConnectorLabel] = toKernel
  given Conversion[BinderLabel, lisa.kernel.fol.FOL.BinderLabel] = toKernel
  given Conversion[FormulaLabel, lisa.kernel.fol.FOL.FormulaLabel] = toKernel

}
