package me.cassayre.florian.masterproject.front.fol.conversions.from

import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions

trait TermConversionsFrom {
  this: TermDefinitions =>

  def fromKernel(label: lisa.kernel.fol.FOL.ConstantFunctionLabel): ConstantFunctionLabel[?] =
    ConstantFunctionLabel.unsafe(label.id, label.arity)
  def fromKernel(label: lisa.kernel.fol.FOL.SchematicFunctionLabel): SchematicFunctionLabel[?] =
    SchematicFunctionLabel.unsafe(label.id, label.arity)
  def fromKernel(label: lisa.kernel.fol.FOL.FunctionLabel): FunctionLabel[?] = label match {
    case constant: lisa.kernel.fol.FOL.ConstantFunctionLabel => fromKernel(constant)
    case schematic: lisa.kernel.fol.FOL.SchematicFunctionLabel => fromKernel(schematic)
  }

  def fromKernel(term: lisa.kernel.fol.FOL.Term): Term = term match {
    case lisa.kernel.fol.FOL.VariableTerm(label) => VariableTerm(VariableLabel(label.id))
    case lisa.kernel.fol.FOL.FunctionTerm(label, args) => FunctionTerm.unsafe(fromKernel(label), args.map(fromKernel))
  }
}
