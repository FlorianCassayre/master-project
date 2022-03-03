package masterproject.parser

import masterproject.parser.ReadingException.LexingException
import masterproject.parser.SCToken
import masterproject.parser.SCToken.*

import scala.util.matching.Regex
import scala.util.parsing.combinator.RegexParsers

private[parser] abstract class SCLexer extends RegexParsers {

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

  private val identifierPattern = "[a-zA-Z_][a-zA-Z0-9_]*"

  protected def identifier: Parser[Identifier] = positioned(
    identifierPattern.r ^^ { str => Identifier(str) }
  )
  protected def schematicIdentifier: Parser[SchematicIdentifier] = positioned(
    (s"\\?$identifierPattern").r ^^ { str => SchematicIdentifier(str.tail) }
  )

  protected def newLine: Parser[NewLine] = positioned(
    "\r?\n".r ^^^ NewLine()
  )

  protected def keywords: Parser[SCToken] = positioned(
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

  // Order matters! Special keywords should be matched before identifiers
  protected def tokens: Parser[Seq[SCToken]] =
    phrase(rep1(keywords | newLine | schematicIdentifier | identifier)) ^^ identity

  def apply(str: String): Seq[SCToken] =
    parse(tokens, str) match {
      case e @ NoSuccess(msg, next) => throw LexingException(e.toString, next.pos, e.toString)
      case Success(result, next) => result
      case e => throw new MatchError(e)
    }
}

object SCLexer {

  private object SCLexerAscii extends SCLexer {

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

  private object SCLexerUnicode extends SCLexer {

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

  private def postProcessor(multiline: Boolean)(tokens: Seq[SCToken]): Seq[SCToken] =
    if(multiline)
      tokens.filter {
        case NewLine() => false
        case _ => true
      }
    else
      tokens

  def lexingAscii(str: String, multiline: Boolean = false): Seq[SCToken] =
    postProcessor(multiline)(SCLexerAscii(str))

  def lexingUnicode(str: String, multiline: Boolean = false): Seq[SCToken] =
    postProcessor(multiline)(SCLexerUnicode(str))

}
