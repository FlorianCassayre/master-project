package me.cassayre.florian.masterproject.front.fol

import me.cassayre.florian.masterproject.front.fol.conversions.to.*
import me.cassayre.florian.masterproject.front.fol.conversions.from.*
import me.cassayre.florian.masterproject.front.fol.definitions.*
import me.cassayre.florian.masterproject.front.fol.ops.*
import me.cassayre.florian.masterproject.front.fol.utils.*

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
