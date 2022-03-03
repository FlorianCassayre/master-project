package masterproject.parser

import lisa.kernel.proof.SequentCalculus.Sequent
import lisa.kernel.fol.FOL.*

object SCReader {

  def readFormulaAscii(str: String, multiline: Boolean = false): Formula =
    SCResolver.resolveFormula(SCParser.parseTermOrFormula(SCLexer.lexingAscii(str, multiline)))

  def readSequentAscii(str: String, multiline: Boolean = false): Sequent =
    SCResolver.resolveSequent(SCParser.parseSequent(SCLexer.lexingAscii(str, multiline)))

}
