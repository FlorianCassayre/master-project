package masterproject.parser

import scala.util.parsing.input.Position

sealed abstract class ReadingException extends Exception {
  val message: String
  val position: Position
  val description: String

  override def toString: String = description
}

object ReadingException {

  case class LexingException(message: String, position: Position, description: String) extends ReadingException
  case class ParsingException(message: String, position: Position, description: String) extends ReadingException
  case class ResolutionException(message: String, position: Position) extends ReadingException {
    override val description: String = s"[$position] $message"
  }

}
