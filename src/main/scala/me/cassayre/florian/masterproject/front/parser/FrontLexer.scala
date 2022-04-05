package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.parser.FrontReadingException.LexingException
import me.cassayre.florian.masterproject.front.parser.FrontToken
import me.cassayre.florian.masterproject.front.parser.FrontToken.*

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

private[parser] trait FrontLexer extends RegexParsers {

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

  private def keywords: Parser[FrontToken] = positioned(
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
      | "\\" ^^^ LocalBinder()
      | "{" ^^^ CurlyBracketOpen()
      | "}" ^^^ CurlyBracketClose()
      | "(" ^^^ ParenthesisOpen()
      | ")" ^^^ ParenthesisClose()
      | "." ^^^ Dot()
      | "," ^^^ Comma()
      | ";" ^^^ Semicolon()
  )

  protected final def standardTokens: Parser[FrontToken] =
    keywords | newLine | schematicIdentifier | identifier

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

object FrontLexer {

  private trait FrontLexerAscii extends FrontLexer {
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
  private object FrontLexerStandardAscii extends FrontLexerAscii

  private trait FrontLexerUnicode extends FrontLexer {
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
