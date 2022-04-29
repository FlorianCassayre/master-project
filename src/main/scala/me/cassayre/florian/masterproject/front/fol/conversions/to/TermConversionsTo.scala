package me.cassayre.florian.masterproject.front.fol.conversions.to

import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions

trait TermConversionsTo {
  this: TermDefinitions =>

  def toKernel(label: VariableLabel): lisa.kernel.fol.FOL.VariableLabel = lisa.kernel.fol.FOL.VariableLabel(label.id)

  def toKernel(label: ConstantFunctionLabel[?]): lisa.kernel.fol.FOL.ConstantFunctionLabel =
    lisa.kernel.fol.FOL.ConstantFunctionLabel(label.id, label.arity)

  def toKernel(label: SchematicFunctionLabel[?]): lisa.kernel.fol.FOL.SchematicFunctionLabel =
    lisa.kernel.fol.FOL.SchematicFunctionLabel(label.id, label.arity)

  def toKernel(label: FunctionLabel[?]): lisa.kernel.fol.FOL.FunctionLabel = label match {
    case constant: ConstantFunctionLabel[?] => toKernel(constant)
    case schematic: SchematicFunctionLabel[?] => toKernel(schematic)
  }

  def toKernel(label: TermLabel): lisa.kernel.fol.FOL.TermLabel = label match {
    case variable: VariableLabel => toKernel(variable)
    case function: FunctionLabel[?] => toKernel(function)
  }

  def toKernel(term: VariableTerm): lisa.kernel.fol.FOL.VariableTerm =
    lisa.kernel.fol.FOL.VariableTerm(toKernel(term.label))

  def toKernel(term: FunctionTerm): lisa.kernel.fol.FOL.FunctionTerm =
    lisa.kernel.fol.FOL.FunctionTerm(toKernel(term.label), term.args.map(toKernel))

  def toKernel(term: Term): lisa.kernel.fol.FOL.Term = term match {
    case variable: VariableTerm => toKernel(variable)
    case function: FunctionTerm => toKernel(function)
  }

  given Conversion[VariableLabel, lisa.kernel.fol.FOL.VariableLabel] = toKernel
  given Conversion[ConstantFunctionLabel[?], lisa.kernel.fol.FOL.ConstantFunctionLabel] = toKernel
  given Conversion[SchematicFunctionLabel[?], lisa.kernel.fol.FOL.SchematicFunctionLabel] = toKernel
  given Conversion[FunctionLabel[?], lisa.kernel.fol.FOL.FunctionLabel] = toKernel
  given Conversion[TermLabel, lisa.kernel.fol.FOL.TermLabel] = toKernel
  given Conversion[VariableTerm, lisa.kernel.fol.FOL.VariableTerm] = toKernel
  given Conversion[FunctionTerm, lisa.kernel.fol.FOL.FunctionTerm] = toKernel
  given Conversion[Term, lisa.kernel.fol.FOL.Term] = toKernel

  given Conversion[(Term, Term), (lisa.kernel.fol.FOL.Term, lisa.kernel.fol.FOL.Term)] = (a, b) => (a, b)

}
