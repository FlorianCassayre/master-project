package me.cassayre.florian.masterproject.front.parser

private[front] sealed abstract class FrontSymbols {
  val Forall: String
  val Exists: String
  val ExistsOne: String
  val Iff: String
  val Implies: String
  val Or: String
  val And: String
  val Exclamation: String
  val Turnstile: String
  val Ellipsis: String
  val Subset: String
  val Membership: String
  val EmptySet: String
  val Equal: String = "="
  val Tilde: String = "~"
  val Backslash: String = "\\"
  val CurlyBracketOpen: String = "{"
  val CurlyBracketClose: String = "}"
  val ParenthesisOpen: String = "("
  val ParenthesisClose: String = ")"
  val Dot: String = "."
  val Comma: String = ","
  val Semicolon: String = ";"
  val QuestionMark: String = "?"
}

private[front] object FrontSymbols {
  object FrontAsciiSymbols extends FrontSymbols {
    override val Forall: String = "forall"
    override val Exists: String = "exists"
    override val ExistsOne: String = "existsone"
    override val Iff: String = "<=>"
    override val Implies: String = "=>"
    override val Or: String = """\/"""
    override val And: String = """/\"""
    override val Exclamation: String = "!"
    override val Turnstile: String = "|-"
    override val Ellipsis: String = "..."
    override val Membership: String = "in"
    override val Subset: String = "sub"
    override val EmptySet: String = "{}"
  }

  object FrontUnicodeSymbols extends FrontSymbols {
    override val Forall: String = "∀"
    override val Exists: String = "∃"
    override val ExistsOne: String = "∃!"
    override val Iff: String = "↔"
    override val Implies: String = "⇒"
    override val Or: String = "∨"
    override val And: String = "∧"
    override val Exclamation: String = "¬"
    override val Turnstile: String = "⊢"
    override val Ellipsis: String = "…"
    override val Membership: String = "∈"
    override val Subset: String = "⊆"
    override val EmptySet: String = "∅"
  }
}
