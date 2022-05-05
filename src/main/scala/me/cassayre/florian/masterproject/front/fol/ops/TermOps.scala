package me.cassayre.florian.masterproject.front.fol.ops

import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions

trait TermOps extends TermDefinitions with CommonOps {

  extension[N <: Arity] (label: FunctionLabel[N])
    def apply(args: FillArgs[Term, N]): FunctionTerm = FunctionTerm.unsafe(label, tuple2seq(args))
  //extension (label: FunctionLabel[2])
  //  def apply(a: Term, b: Term): FunctionTerm = FunctionTerm.unsafe(label, Seq(a, b))
  //extension (label: FunctionLabel[1])
  //  def apply(a: Term): FunctionTerm = FunctionTerm.unsafe(label, Seq(a))
  extension (label: FunctionLabel[0])
    def apply(): FunctionTerm = FunctionTerm.unsafe(label, Seq.empty)

  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply

  given Conversion[ConstantFunctionLabel[0], FunctionTerm] = FunctionTerm.unsafe(_, Seq.empty)
  given Conversion[SchematicFunctionLabel[0], FunctionTerm] = FunctionTerm.unsafe(_, Seq.empty)
  given Conversion[FunctionLabel[0], FunctionTerm] = FunctionTerm.unsafe(_, Seq.empty)

  @deprecated
  given Conversion[Term, TermLabel] = _.label

}
