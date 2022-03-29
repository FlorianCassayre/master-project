package me.cassayre.florian.masterproject.front.fol.ops

import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions

trait TermOps extends CommonOps {
  this: TermDefinitions =>

  extension[N <: Arity] (l: FunctionLabel[N])
    def apply: FillTuple[Term, N] => FunctionTerm[N] = args => FunctionTerm(l, tuple2seq(args))
  extension (l: FunctionLabel[0])
    def apply(): FunctionTerm[0] = FunctionTerm(l, Seq.empty)

  given Conversion[VariableLabel, VariableTerm] = VariableTerm.apply
  given Conversion[FunctionLabel[0], FunctionTerm[0]] = FunctionTerm(_, Seq.empty)

  given Conversion[Term, TermLabel] = _.label

}
