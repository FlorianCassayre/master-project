package masterproject.parser

import masterproject.parser.ReadingException.LexingException
import masterproject.parser.SCToken
import masterproject.parser.SCToken.*

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

private[parser] trait SCLexer extends RegexParsers {

  override def skipWhitespace: Boolean = true
  override protected val whiteSpace: Regex = "[ \t\f]+".r

  protected val SymbolForall: String
  protected val SymbolExists: String
  protected val SymbolExistsOne: String
  protected val SymbolIff: String
  protected val SymbolImplies: String
  protected val SymbolOr: String
  protected val SymbolAnd: String
  protected val SymbolNot: String
  protected val SymbolTurnstile: String
  protected val SymbolSubset: String
  protected val SymbolMembership: String
  protected val SymbolEmptySet: String

  protected def initialIndentation: Parser[InitialIndentation] = positioned(
    " *".r ^^ (str => InitialIndentation(str.length))
  )
  protected def newLine: Parser[NewLineWithIndentation] = positioned(
    "\r?\n *".r ^^ (str => NewLineWithIndentation(str.count(_ == ' ')))
  )

  private val identifierPattern = "[a-zA-Z_][a-zA-Z0-9_]*"

  private def identifier: Parser[Identifier] = positioned(
    identifierPattern.r ^^ (str => Identifier(str))
  )
  private def schematicIdentifier: Parser[SchematicIdentifier] = positioned(
    (s"\\?$identifierPattern").r ^^ (str => SchematicIdentifier(str.tail))
  )

  private def keywords: Parser[SCToken] = positioned(
    SymbolForall ^^^ Forall()
      | SymbolExistsOne ^^^ ExistsOne()
      | SymbolExists ^^^ Exists()
      | SymbolIff ^^^ Iff()
      | SymbolImplies ^^^ Implies()
      | SymbolOr ^^^ Or()
      | SymbolAnd ^^^ And()
      | SymbolNot ^^^ Not()
      | SymbolTurnstile ^^^ Turnstile()
      | SymbolSubset ^^^ Subset()
      | SymbolMembership ^^^ Membership()
      | SymbolEmptySet ^^^ EmptySet()
      | "=" ^^^ Equal()
      | "~" ^^^ SameCardinality()
      | "{" ^^^ CurlyBracketOpen()
      | "}" ^^^ CurlyBracketClose()
      | "(" ^^^ ParenthesisOpen()
      | ")" ^^^ ParenthesisClose()
      | "." ^^^ Dot()
      | "," ^^^ Comma()
      | ";" ^^^ Semicolon()
  )

  protected final def standardTokens: Parser[SCToken] =
    keywords | newLine | schematicIdentifier | identifier

  // Order matters! Special keywords should be matched before identifiers
  protected def tokens: Parser[Seq[SCToken]] =
    phrase(initialIndentation ~ rep(standardTokens) ^^ { case h ~ t => h +: t })

  final def apply(str: String): Seq[SCToken] =
    parse(tokens, str) match {
      case e @ NoSuccess(msg, next) => throw LexingException(e.toString, next.pos)
      case Success(result, next) => result
      case e => throw new MatchError(e)
    }
}

object SCLexer {

  private trait SCLexerExtended extends SCLexer {
    private def integerLiteral: Parser[IntegerLiteral] = positioned(
      "0|-?[1-9][0-9]*".r ^^ { str => IntegerLiteral(str.toInt) }
    )

    private def rules: Parser[RuleName] =
      positioned(
        ("Rewrite"
          | "Hypo."
          | "Cut"
          | "Left ∧"
          | "Left ¬"
          | "Right ∨"
          | "Right ¬"
          | "Left ∃"
          | "Left ∀"
          | "Left ∨"
          | "Right ∃"
          | "Right ∀"
          | "Right ∧"
          | "Right ↔"
          | "Right →"
          | "Weakening"
          | "Left →"
          | "Left ↔"
          | "L. Refl"
          | "R. Refl"
          | "L. SubstEq"
          | "R. SubstEq"
          | "L. SubstIff"
          | "R. SubstIff"
          | "?Fun Instantiation"
          | "?Pred Instantiation"
          | "SCSubproof (hidden)" // FIXME
          | "Subproof"
          | "Import") ^^ RuleName.apply
      )

    override protected def tokens: Parser[Seq[SCToken]] =
      phrase(initialIndentation ~ rep(rules | integerLiteral | standardTokens) ^^ { case h ~ t => h +: t })
  }

  private trait SCLexerAscii extends SCLexer {
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
  }
  private object SCLexerStandardAscii extends SCLexerAscii

  private trait SCLexerUnicode extends SCLexer {
    override protected val SymbolForall: String = "∀"
    override protected val SymbolExists: String = "∃"
    override protected val SymbolExistsOne: String = "∃!"
    override protected val SymbolIff: String = "↔"
    override protected val SymbolImplies: String = "⇒"
    override protected val SymbolOr: String = "∨"
    override protected val SymbolAnd: String = "∧"
    override protected val SymbolNot: String = "¬"
    override protected val SymbolTurnstile: String = "⊢"
    override protected val SymbolMembership: String = "∈"
    override protected val SymbolSubset: String = "⊆"
    override protected val SymbolEmptySet: String = "∅"
  }
  private object SCLexerStandardUnicode extends SCLexerUnicode
  private object SCLexerExtendedUnicode extends SCLexerExtended with SCLexerUnicode

  private def postProcessor(lines: Boolean, indentation: Boolean)(tokens: Seq[SCToken]): Seq[SCToken] =
    val tokensWithEnd = tokens :+ End()
    tokensWithEnd.flatMap {
      case token @ NewLineWithIndentation(n) =>
        val tokenLine = NewLine()
        tokenLine.pos = token.pos
        val tokenIndentation = Indentation(n)
        tokenIndentation.pos = token.pos
        if(indentation)
          Seq(tokenLine, tokenIndentation)
        else if(lines)
          Seq(tokenLine)
        else
          Seq.empty
      case token @ InitialIndentation(n) =>
        val newToken = Indentation(n)
        newToken.pos = token.pos
        if(indentation) Seq(newToken) else Seq.empty
      case other => Seq(other)
    }

  def lexingStandardAscii(str: String, lines: Boolean = false, indentation: Boolean = false): Seq[SCToken] =
    postProcessor(lines, indentation)(SCLexerStandardAscii(str))

  def lexingStandardUnicode(str: String, lines: Boolean = false, indentation: Boolean = false): Seq[SCToken] =
    postProcessor(lines, indentation)(SCLexerStandardUnicode(str))

  def lexingExtendedUnicode(str: String): Seq[SCToken] =
    postProcessor(lines = true, indentation = true)(SCLexerExtendedUnicode(str))

}
