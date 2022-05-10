package me.cassayre.florian.masterproject.front.fol

import me.cassayre.florian.masterproject.front.fol.conversions.to.*
import me.cassayre.florian.masterproject.front.fol.conversions.from.*
import me.cassayre.florian.masterproject.front.fol.definitions.*
import me.cassayre.florian.masterproject.front.fol.ops.*
import me.cassayre.florian.masterproject.front.fol.utils.*
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter

/**
 * The package containing all the definitions and utilities to work with first order logic (FOL).
 */
object FOL extends FormulaDefinitions
  with TermConversionsTo with FormulaConversionsTo
  with TermConversionsFrom with FormulaConversionsFrom
  with TermUtils with FormulaUtils
  with TermOps with FormulaOps {

  override protected def pretty(term: Term): String = FrontPositionedPrinter.prettyTerm(term)
  override protected def pretty(formula: Formula): String = FrontPositionedPrinter.prettyFormula(formula)

  type LabelType = Label
  type SchematicLabelType = SchematicLabel
  type LabeledTreeType[A <: Label] = LabeledTree[A]
  type WithArityType[N <: Arity] = WithArity[N]

}
