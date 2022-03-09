package masterproject.front.fol

import masterproject.front.fol.conversions.*
import masterproject.front.fol.definitions.*
import masterproject.front.fol.ops.*
import masterproject.front.fol.tree.*

object FOL extends FormulaDefinitions
  with TermConversions with FormulaConversions
  with TermTreeFunctions with FormulaTreeFunctions
  with TermOps with FormulaOps
