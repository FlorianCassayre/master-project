package me.cassayre.florian.masterproject.front.fol.ops

import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions

trait TermOps extends CommonOps {
  this: TermDefinitions =>

  extension[N <: Arity] (l: FunctionLabel[N])
    def apply: FillArgs[Term, N] => FunctionTerm = args => FunctionTerm(l, tuple2seq(args))
  extension (l: FunctionLabel[0])
    def apply(): FunctionTerm = FunctionTerm(l, Seq.empty)

  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply
  given Conversion[FunctionLabel[0], FunctionTerm] = FunctionTerm(_, Seq.empty)

  @deprecated
  given Conversion[Term, TermLabel] = _.label

}
