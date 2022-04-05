package me.cassayre.florian.masterproject.front.parser

import scala.util.parsing.input.{Position, Positional}

sealed abstract class FrontParsed extends Positional

private[parser] object FrontParsed {

  case class ParsedSequent(left: Seq[ParsedTopTermOrFormula], right: Seq[ParsedTopTermOrFormula]) extends FrontParsed

  case class ParsedTopTermOrFormula(freeVariables: Seq[String], termOrFormula: ParsedTermOrFormula) extends FrontParsed

  sealed abstract class ParsedTermOrFormula extends FrontParsed

  sealed abstract class ParsedName extends ParsedTermOrFormula {
    val identifier: String
  }
  case class ParsedConstant(identifier: String) extends ParsedName
  case class ParsedSchema(identifier: String) extends ParsedName

  case class ParsedApplication(name: ParsedName, args: Seq[ParsedTermOrFormula]) extends ParsedTermOrFormula

  sealed abstract class ParsedBinaryOperator extends ParsedTermOrFormula {
    val left: ParsedTermOrFormula
    val right: ParsedTermOrFormula
  }
  case class ParsedAnd(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedOr(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedImplies(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedIff(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator

  case class ParsedEqual(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedMembership(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedSubset(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator
  case class ParsedSameCardinality(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedBinaryOperator

  case class ParsedPower(termOrFormula: ParsedTermOrFormula) extends ParsedTermOrFormula
  case class ParsedUnion(termOrFormula: ParsedTermOrFormula) extends ParsedTermOrFormula

  case class ParsedNot(termOrFormula: ParsedTermOrFormula) extends ParsedTermOrFormula

  sealed abstract class ParsedProduct extends ParsedTermOrFormula {
    val left: ParsedTermOrFormula
    val right: ParsedTermOrFormula
  }
  case class ParsedOrderedPair(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedProduct
  case class ParsedSet2(left: ParsedTermOrFormula, right: ParsedTermOrFormula) extends ParsedProduct
  case class ParsedSet1(termOrFormula: ParsedTermOrFormula) extends ParsedTermOrFormula
  case class ParsedSet0() extends ParsedTermOrFormula

  sealed abstract class ParsedBinder extends ParsedTermOrFormula {
    val bound: Seq[String]
    val termOrFormula: ParsedTermOrFormula
  }
  case class ParsedForall(bound: Seq[String], termOrFormula: ParsedTermOrFormula) extends ParsedBinder
  case class ParsedExists(bound: Seq[String], termOrFormula: ParsedTermOrFormula) extends ParsedBinder
  case class ParsedExistsOne(bound: Seq[String], termOrFormula: ParsedTermOrFormula) extends ParsedBinder

  case class ParsedProofStep(stepPosition: Position, indentation: Int, line: Int, ruleName: String, premises: Seq[Int], conclusion: ParsedSequent) extends FrontParsed

  case class ParsedProof(steps: IndexedSeq[ParsedProofStep]) extends FrontParsed

}
