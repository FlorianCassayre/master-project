package me.cassayre.florian.masterproject.front.parser

private[front] case class KernelRuleIdentifiers(symbols: FrontSymbols) {

  private val isLatex: Boolean = symbols.isInstanceOf[FrontSymbols.FrontLatexSymbols.type]

  private val Left: String = "Left"
  private val Right: String = "Right"
  private val Subst: String = "Subst."
  private val Refl: String = "Refl."
  private val Instantiation: String = "Instantiation"
  private val Subproof: String = "Subproof"

  private def symbol(s: String): String = if(isLatex) s"{$s}" else s
  private def text(s: String): String = if(isLatex) raw"\text{$s}" else s
  private def space: String = if(isLatex) "~" else " "
  private def left(s: String): String = s"${text(Left)}$space${symbol(s)}"
  private def right(s: String): String = s"${text(Right)}$space${symbol(s)}"
  private def leftSubst(s: String): String = s"${text(s"$Left $Subst")}$space${symbol(s)}"
  private def rightSubst(s: String): String = s"${text(s"$Right $Subst")}$space${symbol(s)}"

  val Hypothesis: String = text("Hypo.")
  val Cut: String = text("Cut")
  val Rewrite: String = text("Rewrite")
  val Weakening: String = text("Weakening")
  val LeftAnd: String = left(symbols.And)
  val RightAnd: String = right(symbols.And)
  val LeftOr: String = left(symbols.Or)
  val RightOr: String = right(symbols.Or)
  val LeftImplies: String = left(symbols.Implies)
  val RightImplies: String = right(symbols.Implies)
  val LeftIff: String = left(symbols.Iff)
  val RightIff: String = right(symbols.Iff)
  val LeftNot: String = left(symbols.Exclamation)
  val RightNot: String = right(symbols.Exclamation)
  val LeftForall: String = left(symbols.Forall)
  val RightForall: String = right(symbols.Forall)
  val LeftExists: String = left(symbols.Exists)
  val RightExists: String = right(symbols.Exists)
  val LeftExistsOne: String = left(symbols.ExistsOne)
  val RightExistsOne: String = right(symbols.ExistsOne)
  val LeftRefl: String = left(Refl)
  val RightRefl: String = right(Refl)
  val LeftSubstEq: String = leftSubst(symbols.Equal)
  val RightSubstEq: String = rightSubst(symbols.Equal)
  val LeftSubstIff: String = leftSubst(symbols.Iff)
  val RightSubstIff: String = rightSubst(symbols.Iff)
  val FunInstantiation: String = text(s"?Fun. $Instantiation")
  val PredInstantiation: String = text(s"?Pred. $Instantiation")
  val SubproofShown: String = text(Subproof)
  val SubproofHidden: String = text(s"$Subproof (hidden)")
  val Import: String = text("Import")

}
