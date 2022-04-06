package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.parser.FrontResolver
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*

object FrontReader {

  private def lexing(str: String, ascii: Boolean, multiline: Boolean): Seq[FrontToken] = {
    val lexer = if(ascii) FrontLexer.lexingAscii else FrontLexer.lexingUnicode
    lexer(str, !multiline, false)
  }

  def readTerm(str: String, ascii: Boolean = true, toplevel: Boolean = true, multiline: Boolean = false): Term = {
    val tokens = lexing(str, ascii, multiline)
    if(toplevel)
      FrontResolver.resolveTerm(FrontParser.parseTermOrFormula(tokens))
    else
      FrontResolver.resolveTerm(FrontParser.parseTermOrFormula(tokens))
  }

  def readFormula(str: String, ascii: Boolean = true, toplevel: Boolean = true, multiline: Boolean = false): Formula = {
    val tokens = lexing(str, ascii, multiline)
    if(toplevel)
      FrontResolver.resolveFormula(FrontParser.parseTopTermOrFormula(tokens))
    else
      FrontResolver.resolveFormula(FrontParser.parseTermOrFormula(tokens))
  }

  def readSequent(str: String, ascii: Boolean = true, multiline: Boolean = false): Sequent =
    FrontResolver.resolveSequent(FrontParser.parseSequent(lexing(str, ascii, multiline)))

  def readPartialSequent(str: String, ascii: Boolean = true, multiline: Boolean = false): PartialSequent =
    FrontResolver.resolvePartialSequent(FrontParser.parsePartialSequent(lexing(str, ascii, multiline)))



  private def mkString(sc: StringContext, args: Seq[Any]): String = {
    assert(sc.parts.size == args.size + 1)
    sc.parts.zip(args.map(_.toString) :+ "").flatMap { case (p, a) => Seq(p, a) }.mkString
  }

  extension (sc: StringContext)
    def term(args: Any*): Term = readTerm(mkString(sc, args))
    def formula(args: Any*): Formula = readFormula(mkString(sc, args))
    def sequent(args: Any*): Sequent = readSequent(mkString(sc, args))
    def partial(args: Any*): PartialSequent = readPartialSequent(mkString(sc, args))

}
