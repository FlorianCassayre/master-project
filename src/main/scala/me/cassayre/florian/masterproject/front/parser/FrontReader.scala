package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.parser.FrontResolver
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*

object FrontReader {

  def readFormulaAscii(str: String, toplevel: Boolean = true, multiline: Boolean = false): Formula = {
    val tokens = FrontLexer.lexingAscii(str, lines = !multiline)
    if(toplevel)
      FrontResolver.resolveFormula(FrontParser.parseTopTermOrFormula(tokens))
    else
      FrontResolver.resolveFormula(FrontParser.parseTermOrFormula(tokens))
  }

  def readSequentAscii(str: String, multiline: Boolean = false): Sequent =
    FrontResolver.resolveSequent(FrontParser.parseSequent(FrontLexer.lexingAscii(str, lines = !multiline)))

}
