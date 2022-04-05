package me.cassayre.florian.masterproject.front.parser

import scala.util.parsing.input.Position

sealed abstract class FrontReadingException extends Exception {
  val message: String
  val position: Position

  override def toString: String = s"[$position] failure: $message\n\n${position.longString}"
}

object FrontReadingException {

  case class LexingException(message: String, position: Position) extends FrontReadingException
  case class ParsingException(message: String, position: Position) extends FrontReadingException
  case class ResolutionException(message: String, position: Position) extends FrontReadingException

}
