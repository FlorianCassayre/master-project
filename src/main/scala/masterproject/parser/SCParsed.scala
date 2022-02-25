package masterproject.parser

import scala.util.parsing.input.Positional

object SCParsed {

  case class SCParsedSequent(left: Seq[SCParsedTermOrFormula], right: Seq[SCParsedTermOrFormula]) extends Positional

  sealed abstract class SCParsedTermOrFormula extends Positional

  sealed abstract class SCParsedName extends SCParsedTermOrFormula {
    val identifier: String
  }
  case class SCParsedConstant(identifier: String) extends SCParsedName
  case class SCParsedSchema(identifier: String) extends SCParsedName

  case class SCParsedApplication(name: SCParsedName, args: Seq[SCParsedTermOrFormula]) extends SCParsedTermOrFormula

  sealed abstract class SCParsedBinaryOperator extends SCParsedTermOrFormula {
    val left: SCParsedTermOrFormula
    val right: SCParsedTermOrFormula
  }
  case class SCParsedAnd(left: SCParsedTermOrFormula, right: SCParsedTermOrFormula) extends SCParsedBinaryOperator
  case class SCParsedOr(left: SCParsedTermOrFormula, right: SCParsedTermOrFormula) extends SCParsedBinaryOperator
  case class SCParsedImplies(left: SCParsedTermOrFormula, right: SCParsedTermOrFormula) extends SCParsedBinaryOperator
  case class SCParsedIff(left: SCParsedTermOrFormula, right: SCParsedTermOrFormula) extends SCParsedBinaryOperator

  case class SCParsedEqual(left: SCParsedTermOrFormula, right: SCParsedTermOrFormula) extends SCParsedBinaryOperator

  case class SCParsedNot(termOrFormula: SCParsedTermOrFormula) extends SCParsedTermOrFormula

  sealed abstract class SCParsedBinder extends SCParsedTermOrFormula {
    val bound: String
    val termOrFormula: SCParsedTermOrFormula
  }
  case class SCParsedForall(bound: String, termOrFormula: SCParsedTermOrFormula) extends SCParsedBinder
  case class SCParsedExists(bound: String, termOrFormula: SCParsedTermOrFormula) extends SCParsedBinder
  case class SCParsedExistsOne(bound: String, termOrFormula: SCParsedTermOrFormula) extends SCParsedBinder
  
}
