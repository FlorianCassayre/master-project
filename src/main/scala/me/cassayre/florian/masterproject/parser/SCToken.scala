package me.cassayre.florian.masterproject.parser

import scala.util.parsing.input.Positional

sealed abstract class SCToken extends Positional

private[parser] object SCToken {

  case class Identifier(identifier: String) extends SCToken
  case class SchematicIdentifier(identifier: String) extends SCToken

  case class IntegerLiteral(value: Int) extends SCToken

  case class Indentation(spaces: Int) extends SCToken

  case class NewLineWithIndentation(spaces: Int) extends SCToken
  case class InitialIndentation(spaces: Int) extends SCToken

  // The reason these *must* be case classes is because they extend `Positional`,
  // which contains a position attribute (that shouldn't be shared between instances)

  case class Turnstile() extends SCToken
  case class And() extends SCToken
  case class Or() extends SCToken
  case class Implies() extends SCToken
  case class Iff() extends SCToken
  case class Equal() extends SCToken
  case class Membership() extends SCToken
  case class Subset() extends SCToken
  case class SameCardinality() extends SCToken
  case class Forall() extends SCToken
  case class Exists() extends SCToken
  case class ExistsOne() extends SCToken
  case class Not() extends SCToken
  case class EmptySet() extends SCToken
  case class LocalBinder() extends SCToken

  case class CurlyBracketOpen() extends SCToken
  case class CurlyBracketClose() extends SCToken
  case class ParenthesisOpen() extends SCToken
  case class ParenthesisClose() extends SCToken

  case class Dot() extends SCToken
  case class Comma() extends SCToken
  case class Semicolon() extends SCToken

  case class RuleName(name: String) extends SCToken

  case class NewLine() extends SCToken

  case class End() extends SCToken

}
