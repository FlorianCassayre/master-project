package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.parser.FrontReadingException.LexingException
import me.cassayre.florian.masterproject.front.parser.FrontToken
import me.cassayre.florian.masterproject.front.parser.FrontToken.*
import me.cassayre.florian.masterproject.front.parser.FrontSymbols

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

private trait FrontLexer extends RegexParsers {

  override def skipWhitespace: Boolean = true
  override protected val whiteSpace: Regex = "[ \t\f]+".r

  protected val S: FrontSymbols

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
    (raw"\${S.QuestionMark}$identifierPattern").r ^^ (str => SchematicIdentifier(str.tail))
  )
  private def schematicConnectorIdentifier: Parser[SchematicConnectorIdentifier] = positioned(
    (raw"\${S.QuestionMark}\${S.QuestionMark}$identifierPattern").r ^^ (str => SchematicConnectorIdentifier(str.tail.tail))
  )

  private def keywords: Parser[FrontToken] = positioned(
    S.Forall ^^^ Forall()
      | S.ExistsOne ^^^ ExistsOne()
      | S.Exists ^^^ Exists()
      | S.Iff ^^^ Iff()
      | S.Implies ^^^ Implies()
      | S.Or ^^^ Or()
      | S.And ^^^ And()
      | S.Exclamation ^^^ Not()
      | S.Turnstile ^^^ Turnstile()
      | S.Ellipsis ^^^ Ellipsis()
      | S.Subset ^^^ Subset()
      | S.Membership ^^^ Membership()
      | S.EmptySet ^^^ EmptySet()
      | S.Equal ^^^ Equal()
      | S.Tilde ^^^ SameCardinality()
      | S.Backslash ^^^ LocalBinder()
      | S.CurlyBracketOpen ^^^ CurlyBracketOpen()
      | S.CurlyBracketClose ^^^ CurlyBracketClose()
      | S.ParenthesisOpen ^^^ ParenthesisOpen()
      | S.ParenthesisClose ^^^ ParenthesisClose()
      | S.Dot ^^^ Dot()
      | S.Comma ^^^ Comma()
      | S.Semicolon ^^^ Semicolon()
  )

  protected final def standardTokens: Parser[FrontToken] =
    keywords | newLine | schematicConnectorIdentifier | schematicIdentifier | identifier

  // Order matters! Special keywords should be matched before identifiers
  protected def tokens: Parser[Seq[FrontToken]] =
    phrase(initialIndentation ~ rep(standardTokens) ^^ { case h ~ t => h +: t })

  final def apply(str: String): Seq[FrontToken] =
    parse(tokens, str) match {
      case e @ NoSuccess(msg, next) => throw LexingException(e.toString, next.pos)
      case Success(result, next) => result
      case e => throw new MatchError(e)
    }
}

/**
 * The lexer converts a sequence of characters into low-level tokens ([[FrontToken]]), for instance identifiers, symbols, separators.
 */
object FrontLexer {

  private trait FrontLexerAscii extends FrontLexer {
    override protected val S: FrontSymbols = FrontSymbols.FrontAsciiSymbols
  }
  private object FrontLexerStandardAscii extends FrontLexerAscii

  private trait FrontLexerUnicode extends FrontLexer {
    override protected val S: FrontSymbols = FrontSymbols.FrontUnicodeSymbols
  }
  private object FrontLexerStandardUnicode extends FrontLexerUnicode

  private def postProcessor(lines: Boolean, indentation: Boolean)(tokens: Seq[FrontToken]): Seq[FrontToken] =
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

  def lexingAscii(str: String, lines: Boolean = false, indentation: Boolean = false): Seq[FrontToken] =
    postProcessor(lines, indentation)(FrontLexerStandardAscii(str))

  def lexingUnicode(str: String, lines: Boolean = false, indentation: Boolean = false): Seq[FrontToken] =
    postProcessor(lines, indentation)(FrontLexerStandardUnicode(str))

}
