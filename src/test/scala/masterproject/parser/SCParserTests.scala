package masterproject.parser

import org.scalatest.funsuite.AnyFunSuite

import scala.util.Try

class SCParserTests extends AnyFunSuite {

  test("parser positive examples") {
    Seq[String](
      "|- a",
      "a |- b",
      """(a /\ b => ((c <=> d))) |- exists x. f(x)""",
      "forall x,y    , z.exists  w . f(g(w), (x),y)|-a",
      "|- {}={x, {{},y}}"
    ).foreach(s => SCResolver.resolveSequent(SCAsciiParser.parseSequent(s)))
  }

  test("parser negative examples") {
    Seq[String](
      "",
      "|--",
      "a",
      "a |- b |- c",
      "|- w = {x,y,z}"
    ).foreach(s => Try(SCResolver.resolveSequent(SCAsciiParser.parseSequent(s))).isFailure)
  }

}
