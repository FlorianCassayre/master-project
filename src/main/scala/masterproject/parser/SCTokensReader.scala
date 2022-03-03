package masterproject.parser

import scala.util.parsing.input.{Reader, Position, NoPosition}

private[parser] class SCTokensReader(tokens: Seq[SCToken]) extends Reader[SCToken] {
  override def first: SCToken = tokens.head
  override def atEnd: Boolean = tokens.isEmpty
  override def pos: Position = NoPosition
  override def rest: Reader[SCToken] = new SCTokensReader(tokens.tail)
}
