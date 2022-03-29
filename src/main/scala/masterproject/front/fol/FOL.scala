package masterproject.front.fol

import masterproject.front.fol.conversions.to.*
import masterproject.front.fol.conversions.from.*
import masterproject.front.fol.definitions.*
import masterproject.front.fol.ops.*
import masterproject.front.fol.utils.*

object FOL extends FormulaDefinitions
  with TermConversionsTo with FormulaConversionsTo
  with TermConversionsFrom with FormulaConversionsFrom
  with TermUtils with FormulaUtils
  with TermOps with FormulaOps {

  type LabelType = Label
  type SchematicLabelType = SchematicLabel
  type LabeledTreeType[A <: Label] = LabeledTree[A]
  type WithArityType[N <: Arity] = WithArity[N]

}
