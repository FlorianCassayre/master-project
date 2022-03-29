package me.cassayre.florian.masterproject.parser

import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof

object SCReader {

  def readFormulaAscii(str: String, toplevel: Boolean = true, multiline: Boolean = false): Formula = {
    val tokens = SCLexer.lexingStandardAscii(str, lines = !multiline)
    if(toplevel)
      SCResolver.resolveFormula(SCParser.parseTopTermOrFormula(tokens))
    else
      SCResolver.resolveFormula(SCParser.parseTermOrFormula(tokens))
  }

  def readSequentAscii(str: String, multiline: Boolean = false): Sequent =
    SCResolver.resolveSequent(SCParser.parseSequent(SCLexer.lexingStandardAscii(str, lines = !multiline)))

  def readProof(str: String): SCProof =
    SCResolver.resolveProof(SCParser.parseProof(SCLexer.lexingExtendedUnicode(str)))

}
