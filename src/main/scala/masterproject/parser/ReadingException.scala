package masterproject.parser

import scala.util.parsing.input.Position

sealed abstract class ReadingException extends Exception {
  val message: String
  val position: Position

  override def toString: String = s"[$position] failure: $message\n\n${position.longString}"
}

object ReadingException {

  case class LexingException(message: String, position: Position) extends ReadingException
  case class ParsingException(message: String, position: Position) extends ReadingException
  case class ResolutionException(message: String, position: Position) extends ReadingException

}
