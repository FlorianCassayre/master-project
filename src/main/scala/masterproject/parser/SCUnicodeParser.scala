package masterproject.parser

import masterproject.parser.SCAbstractParser

object SCUnicodeParser extends SCAbstractParser {

  override protected val SymbolForall: String = "∀"
  override protected val SymbolExists: String = "∃"
  override protected val SymbolExistsOne: String = "∃!"
  override protected val SymbolIff: String = "↔"
  override protected val SymbolImplies: String = "→"
  override protected val SymbolOr: String = "∨"
  override protected val SymbolAnd: String = "∧"
  override protected val SymbolNot: String = "¬"
  override protected val SymbolTurnstile: String = "⊢"
  override protected val SymbolMembership: String = "∈"
  override protected val SymbolSubset: String = "⊆"
  override protected val SymbolEmptySet: String = "∅"

  lexical.delimiters ++= Seq(
    SymbolForall, SymbolExists, SymbolExistsOne, SymbolIff, SymbolImplies, SymbolOr, SymbolAnd, SymbolNot, SymbolTurnstile, SymbolMembership, SymbolSubset, SymbolEmptySet
  )

}
