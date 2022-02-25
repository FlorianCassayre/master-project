package masterproject.parser

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import masterproject.parser.SCParsed.*

import scala.util.Try

abstract class SCAbstractParser extends StandardTokenParsers {

  protected val SymbolForall: String
  protected val SymbolExists: String
  protected val SymbolExistsOne: String
  protected val SymbolIff: String
  protected val SymbolImplies: String
  protected val SymbolOr: String
  protected val SymbolAnd: String
  protected val SymbolNot: String
  protected val SymbolTurnstile: String

  lexical.delimiters ++= Seq("=", ".", "(", ")", "?", ";", ",")

  private def identifier = ident

  private def variableOrSchema: Parser[SCParsedName] =
    positioned(identifier ^^ SCParsedConstant.apply) | positioned("?" ~> identifier ^^ SCParsedSchema.apply)

  def binder: Parser[SCParsedTermOrFormula] = positioned(
    (SymbolForall ^^^ SCParsedExists.apply | SymbolExists ^^^ SCParsedExists.apply | SymbolExistsOne ^^^ SCParsedExists.apply) ~
      identifier ~ "." ~ termOrFormula ^^ { case f ~ b ~ _ ~ t => f(b, t) }
  )

  def termOrFormula: Parser[SCParsedTermOrFormula] = positioned(
    termOrFormulaIff |
      binder
    )

  def termOrFormulaIff: Parser[SCParsedTermOrFormula] =
    positioned(termOrFormulaImplies ~ rep(SymbolIff ~> termOrFormulaImplies) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedIff.apply) })
  def termOrFormulaImplies: Parser[SCParsedTermOrFormula] =
    positioned(termOrFormulaOr ~ rep(SymbolImplies ~> termOrFormulaOr) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedImplies.apply) })
  def termOrFormulaOr: Parser[SCParsedTermOrFormula] =
    positioned(termOrFormulaAnd ~ rep(SymbolOr ~> termOrFormulaAnd) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedOr.apply) })
  def termOrFormulaAnd: Parser[SCParsedTermOrFormula] =
    positioned(termOrFormulaEqual ~ rep(SymbolAnd ~> termOrFormulaEqual) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedAnd.apply) })
  def termOrFormulaEqual: Parser[SCParsedTermOrFormula] =
    positioned(termNot ~ rep("=" ~> termNot) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedEqual.apply) })

  def termNot: Parser[SCParsedTermOrFormula] =
    positioned(
      atom
      | SymbolNot ~> atom ^^ SCParsedNot.apply
    )

  private def atom: Parser[SCParsedTermOrFormula] = positioned(
    variableOrSchema ~ ("(" ~> rep1sep(termOrFormula, ",") <~ ")").? ^^ { case v ~ argsOpt => argsOpt.map(SCParsedApplication(v, _)).getOrElse(v) }
      | "(" ~> termOrFormula <~ ")"
  )

  private def termOrFormulaSequence: Parser[Seq[SCParsedTermOrFormula]] = repsep(termOrFormula, ";")

  def sequent: Parser[SCParsedSequent] = termOrFormulaSequence ~ SymbolTurnstile ~ termOrFormulaSequence ^^ { case l ~ _ ~ r => SCParsedSequent(l, r) }


  private def parse[T](parser: Parser[T])(s: String): T = {
    val tokens = new lexical.Scanner(s)
    phrase(parser)(tokens) match {
      case Success(tree, _) => tree
      case e => throw new Exception(e.toString)
    }
  }

  def parseSequent(s: String): SCParsedSequent = parse(sequent)(s)

  def parseTermOrFormula(s: String): SCParsedTermOrFormula = parse(termOrFormula)(s)
}
