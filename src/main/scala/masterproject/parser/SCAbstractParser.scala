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
  protected val SymbolSubset: String
  protected val SymbolMembership: String
  protected val SymbolEmptySet: String

  lexical.delimiters ++= Seq("=", ".", "(", ")", "{", "}", "?", ";", ",", "~")

  lexical.reserved ++= Seq("P", "U")

  private def identifier = ident

  private def variableOrSchema: Parser[SCParsedName] =
    positioned(identifier ^^ SCParsedConstant.apply) | positioned("?" ~> identifier ^^ SCParsedSchema.apply)

  def binder: Parser[SCParsedTermOrFormula] = positioned(
    (SymbolForall ^^^ SCParsedForall.apply | SymbolExists ^^^ SCParsedExists.apply | SymbolExistsOne ^^^ SCParsedExistsOne.apply) ~
      rep1sep(identifier, ",") ~ "." ~ termOrFormula ^^ { case f ~ bs ~ _ ~ t => f(bs, t) }
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
    positioned(termOrFormulaPredicate ~ rep(SymbolAnd ~> termOrFormulaPredicate) ^^ { case h ~ t => (h +: t).reduceRight(SCParsedAnd.apply) })
  def termOrFormulaPredicate: Parser[SCParsedTermOrFormula] =
    positioned(termNot ~
      rep((SymbolMembership ^^^ SCParsedMembership.apply | SymbolSubset ^^^ SCParsedSubset.apply | "~" ^^^ SCParsedSameCardinality.apply | "=" ^^^ SCParsedEqual.apply) ~
        termNot) ^^ {
      case t1 ~ ts => ts.foldRight(t1) { case (f ~ tr, tl) => f(tl, tr) }
    })

  def termNot: Parser[SCParsedTermOrFormula] =
    positioned(
      atom
      | SymbolNot ~> atom ^^ SCParsedNot.apply
    )

  private def atom: Parser[SCParsedTermOrFormula] = positioned(
    ("P" ^^^ SCParsedPower.apply | "U" ^^^ SCParsedUnion.apply) ~ "(" ~ termOrFormula ~ ")" ^^ {
      case f ~ _ ~ t ~ _ => f(t)
    }
      | variableOrSchema ~ ("(" ~> rep1sep(termOrFormula, ",") <~ ")").? ^^ {
      case v ~ argsOpt => argsOpt.map(SCParsedApplication(v, _)).getOrElse(v)
    }
      | "(" ~ termOrFormula ~ ("," ~> termOrFormula <~ ")").? ~ ")" ^^ { case _ ~ t1 ~ opt ~ _ => opt match {
      case Some(t2) => SCParsedOrderedPair(t1, t2)
      case None => t1
    } }
      | "{" ~> (termOrFormula ~ ("," ~> termOrFormula).?).? <~ "}" ^^ {
      case Some(t1 ~ opt2) =>
        opt2 match {
          case Some(t2) => SCParsedSet2(t1, t2)
          case None => SCParsedSet1(t1)
        }
      case None => SCParsedSet0
    }
      | SymbolEmptySet ^^^ SCParsedSet0
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
