package masterproject.parser

import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.fol.FOL.*
import lisa.kernel.proof.SCProof

object SCReader {

  def readFormulaAscii(str: String, multiline: Boolean = false): Formula =
    SCResolver.resolveFormula(SCParser.parseTermOrFormula(SCLexer.lexingStandardAscii(str, lines = !multiline)))

  def readSequentAscii(str: String, multiline: Boolean = false): Sequent =
    SCResolver.resolveSequent(SCParser.parseSequent(SCLexer.lexingStandardAscii(str, lines = !multiline)))

  def readProof(str: String): SCProof =
    SCResolver.resolveProof(SCParser.parseProof(SCLexer.lexingExtendedUnicode(str)))

}
