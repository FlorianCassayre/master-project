package masterproject.parser

object SCAsciiParser extends SCAbstractParser {

  override protected val SymbolForall: String = "forall"
  override protected val SymbolExists: String = "exists"
  override protected val SymbolExistsOne: String = "existsone"
  override protected val SymbolIff: String = "<=>"
  override protected val SymbolImplies: String = "=>"
  override protected val SymbolOr: String = """\/"""
  override protected val SymbolAnd: String = """/\"""
  override protected val SymbolNot: String = "!"
  override protected val SymbolTurnstile: String = "|-"
  override protected val SymbolMembership: String = "in"
  override protected val SymbolSubset: String = "sub"
  override protected val SymbolEmptySet: String = "empty"

  lexical.delimiters ++= Seq(
    SymbolIff, SymbolImplies, SymbolOr, SymbolAnd, SymbolNot, SymbolTurnstile
  )

  lexical.reserved ++= Seq(
    SymbolForall, SymbolExists, SymbolExistsOne, SymbolMembership, SymbolSubset, SymbolEmptySet
  )

}
