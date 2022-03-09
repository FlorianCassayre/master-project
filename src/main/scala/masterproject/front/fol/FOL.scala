package masterproject.front.fol

import masterproject.front.fol.conversions.*
import masterproject.front.fol.definitions.*
import masterproject.front.fol.ops.*
import masterproject.front.fol.utils.*

object FOL extends FormulaDefinitions
  with TermConversions with FormulaConversions
  with TermUtils with FormulaUtils
  with TermOps with FormulaOps {

  type LabelType = Label
  type SchematicLabelType = SchematicLabel
  type LabeledTreeType[A <: Label] = LabeledTree[A]
  type ArityType = Arity
  type WithArityType[N <: Arity] = WithArity[N]

}
