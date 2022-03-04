package masterproject.parser

import masterproject.parser.ReadingException.ParsingException
import masterproject.parser.SCToken
import masterproject.parser.SCToken.*
import masterproject.parser.SCParsed
import masterproject.parser.SCParsed.*

import scala.util.parsing.combinator.Parsers

private[parser] object SCParser extends Parsers {

  override type Elem = SCToken

  private def identifier: Parser[Identifier] =
    positioned(accept("identifier", { case id: Identifier => id }))
  private def schematicIdentifier: Parser[SchematicIdentifier] =
    positioned(accept("schematic identifier", { case id: SchematicIdentifier => id }))

  private def identifierOrSchematic: Parser[Identifier | SchematicIdentifier] =
    positioned(identifier | schematicIdentifier)

  private def integerLiteral: Parser[IntegerLiteral] =
    positioned(accept("integer literal", { case lit: IntegerLiteral => lit }))
  private def ruleName: Parser[RuleName] =
    positioned(accept("rule", { case rule: RuleName => rule }))

  private def binder: Parser[ParsedTermOrFormula] = positioned(
    (Forall() ^^^ ParsedForall.apply | Exists() ^^^ ParsedExists.apply | ExistsOne() ^^^ ParsedExistsOne.apply) ~
      rep1sep(identifier, Comma()) ~ Dot() ~ termOrFormula ^^ { case f ~ bs ~ _ ~ t => f(bs.map(_.identifier), t) }
  )

  private def termOrFormula: Parser[ParsedTermOrFormula] = positioned(
   termOrFormulaIff |
      binder
  )

  private def termOrFormulaIff: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaImplies ~ rep(Iff() ~> termOrFormulaImplies) ^^ { case h ~ t => (h +: t).reduceRight(ParsedIff.apply) })
  private def termOrFormulaImplies: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaOr ~ rep(Implies() ~> termOrFormulaOr) ^^ { case h ~ t => (h +: t).reduceRight(ParsedImplies.apply) })
  private def termOrFormulaOr: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaAnd ~ rep(Or() ~> termOrFormulaAnd) ^^ { case h ~ t => (h +: t).reduceRight(ParsedOr.apply) })
  private def termOrFormulaAnd: Parser[ParsedTermOrFormula] =
    positioned(termOrFormulaPredicate ~ rep(And() ~> termOrFormulaPredicate) ^^ { case h ~ t => (h +: t).reduceRight(ParsedAnd.apply) })
  private def termOrFormulaPredicate: Parser[ParsedTermOrFormula] =
    positioned(termNot ~
      rep((Membership() ^^^ ParsedMembership.apply | Subset() ^^^ ParsedSubset.apply | SameCardinality() ^^^ ParsedSameCardinality.apply | Equal() ^^^ ParsedEqual.apply) ~
        termNot) ^^ {
      case t1 ~ ts => ts.foldRight(t1) { case (f ~ tr, tl) => f(tl, tr) }
    })

  private def termNot: Parser[ParsedTermOrFormula] =
    positioned(
      atom
        | Not() ~> atom ^^ ParsedNot.apply
    )

  private def atom: Parser[ParsedTermOrFormula] = positioned(
    (Identifier("P") ^^^ ParsedPower.apply | Identifier("U") ^^^ ParsedUnion.apply) ~ ParenthesisOpen() ~ termOrFormula ~ ParenthesisClose() ^^ {
      case f ~ _ ~ t ~ _ => f(t)
    }
      | identifierOrSchematic ~ (ParenthesisOpen() ~> rep1sep(termOrFormula, Comma()) <~ ParenthesisClose()).? ^^ {
      case v ~ argsOpt =>
        val name = v match {
          case Identifier(identifier) => ParsedConstant(identifier)
          case SchematicIdentifier(identifier) => ParsedSchema(identifier)
        }
        argsOpt.map(ParsedApplication(name, _)).getOrElse(name)
      }
      | ParenthesisOpen() ~ termOrFormula ~ (Comma() ~> termOrFormula <~ ParenthesisClose()).? ~ ParenthesisClose() ^^ { case _ ~ t1 ~ opt ~ _ => opt match {
      case Some(t2) => ParsedOrderedPair(t1, t2)
      case None => t1
    } }
      | CurlyBracketOpen() ~> (termOrFormula ~ (Comma() ~> termOrFormula).?).? <~ CurlyBracketClose() ^^ {
      case Some(t1 ~ opt2) =>
        opt2 match {
          case Some(t2) => ParsedSet2(t1, t2)
          case None => ParsedSet1(t1)
        }
      case None => ParsedSet0()
    }
      | EmptySet() ^^^ ParsedSet0()
  )

  private def termOrFormulaSequence: Parser[Seq[ParsedTermOrFormula]] =
    repsep(termOrFormula, Semicolon())

  private def sequent: Parser[ParsedSequent] =
    positioned(termOrFormulaSequence ~ Turnstile() ~ termOrFormulaSequence ^^ { case l ~ _ ~ r => ParsedSequent(l, r) })

  private def proofStep: Parser[ParsedProofStep] = positioned(
    integerLiteral ~ ruleName ~ repsep(integerLiteral, Comma()) ~ sequent ^^ {
      case l ~ r ~ p ~ s => ParsedProofStep(l.value, r.name, p.map(_.value), s)
    }
  )

  private def proof: Parser[ParsedProof] = positioned(
    NewLine().* ~> rep1sep(proofStep, NewLine()) <~ NewLine().* ^^ (seq => ParsedProof(seq.toIndexedSeq))
  )


  private def parse[T](parser: Parser[T])(tokens: Seq[SCToken]): T = {
    val reader = new SCTokensReader(tokens)
    parser(reader) match {
      case e @ NoSuccess(msg, next) => throw ParsingException(msg, next.pos)
      case Success(result, next) => result
      case e => throw new MatchError(e)
    }
  }

  def parseTermOrFormula(tokens: Seq[SCToken]): ParsedTermOrFormula =
    parse(positioned(termOrFormula <~ End()))(tokens)

  def parseSequent(tokens: Seq[SCToken]): ParsedSequent =
    parse(positioned(sequent <~ End()))(tokens)

  def parseProof(tokens: Seq[SCToken]): ParsedProof =
    parse(positioned(proof <~ End()))(tokens)

}
