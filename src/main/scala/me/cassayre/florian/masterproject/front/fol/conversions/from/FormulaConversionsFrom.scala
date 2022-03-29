package me.cassayre.florian.masterproject.front.fol.conversions.from

import me.cassayre.florian.masterproject.front.fol.conversions.FrontKernelMappings
import me.cassayre.florian.masterproject.front.fol.definitions.FormulaDefinitions

trait FormulaConversionsFrom extends TermConversionsFrom with FrontKernelMappings {
  this: FormulaDefinitions =>

  def fromKernel(label: lisa.kernel.fol.FOL.ConstantPredicateLabel): ConstantPredicateLabel[?] =
    predicatesFrom.getOrElse(label, ConstantPredicateLabel(label.id, label.arity))
  def fromKernel(label: lisa.kernel.fol.FOL.SchematicPredicateLabel): SchematicPredicateLabel[?] =
    SchematicPredicateLabel(label.id, label.arity)
  def fromKernel(label: lisa.kernel.fol.FOL.PredicateLabel): PredicateLabel[?] = label match {
    case constant: lisa.kernel.fol.FOL.ConstantPredicateLabel => fromKernel(constant)
    case schematic: lisa.kernel.fol.FOL.SchematicPredicateLabel => fromKernel(schematic)
  }

  def fromKernel(label: lisa.kernel.fol.FOL.ConnectorLabel): ConstantConnectorLabel[?] = connectorsFrom(label)

  def fromKernel(formula: lisa.kernel.fol.FOL.Formula): Formula = formula match {
    case lisa.kernel.fol.FOL.PredicateFormula(label, args) => PredicateFormula(fromKernel(label), args.map(fromKernel))
    case lisa.kernel.fol.FOL.ConnectorFormula(label, args) => ConnectorFormula(fromKernel(label), args.map(fromKernel))
    case lisa.kernel.fol.FOL.BinderFormula(label, bound, inner) => BinderFormula(bindersFrom(label), VariableLabel(bound.id), fromKernel(inner))
  }
}
