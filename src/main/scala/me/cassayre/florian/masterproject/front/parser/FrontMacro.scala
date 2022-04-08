package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter

// Note: on Intellij you may want to disable syntax highlighting for this file
// ("File Types" => "Text" => "Ignored Files and Folders", add "FrontMacro.scala")

object FrontMacro {

  import scala.quoted.*

  // https://github.com/lampepfl/dotty/issues/8577#issuecomment-1014729373

  extension (inline sc: StringContext)
    transparent inline def term: Any = ${ SIParts.scMacro[TermParts]('sc) }
    transparent inline def formula: Any = ${ SIParts.scMacro[FormulaParts]('sc) }
    transparent inline def sequent: Any = ${ SIParts.scMacro[SequentParts]('sc) }
    transparent inline def partial: Any = ${ SIParts.scMacro[PartialSequentParts]('sc) }

  class TermParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Term = ${ termApplyMacro('parts, 'args) }
    //transparent inline def unapplySeq(inline arg: Any): Option[Seq[Any]] = ${ termUnapplyMacro('parts, 'arg) }
  }
  class FormulaParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Formula = ${ formulaApplyMacro('parts, 'args) }
  }
  class SequentParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): Sequent = ${ sequentApplyMacro('parts, 'args) }
  }
  class PartialSequentParts[P <: Tuple](parts: P) {
    transparent inline def apply(inline args: Any*): PartialSequent = ${ partialSequentApplyMacro('parts, 'args) }
  }

  trait SIParts[P <: Tuple](parts: P)
  object SIParts {
    def scMacro[SI[_ <: Tuple]](sc: Expr[StringContext])(using Quotes, Type[SI]): Expr[Any] = {
      import quotes.reflect.*
      val '{StringContext(${Varargs(args)}*)} = sc
      val tplExpr = Expr.ofTupleFromSeq(args)
      val tplTpe = tplExpr.asTerm.tpe
      val AppliedType(siTpe, _) = TypeRepr.of[SI[Tuple]]
      val siSym = siTpe.typeSymbol
      val siTree =
        New(TypeTree.of[SI[Tuple]])
          .select(siSym.primaryConstructor)
          .appliedToType(tplTpe)
          .appliedTo(tplExpr.asTerm)
      siTree.asExpr
    }
  }


  /*private def termUnapplyMacro[P <: Tuple](parts: Expr[P], arg: Expr[Any])(using Quotes, Type[P]): Expr[Option[Seq[Any]]] = {
    '{ None: Option[Seq[Term]] }
  }*/


  private def termApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Term] =
    '{ FrontReader.readTerm(${rawStringMacro(parts, args)}) }
  private def formulaApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Formula] =
    '{ FrontReader.readFormula(${rawStringMacro(parts, args)}) }
  private def sequentApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Sequent] =
    '{ FrontReader.readSequent(${rawStringMacro(parts, args)}) }
  private def partialSequentApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[PartialSequent] =
    '{ FrontReader.readPartialSequent(${rawStringMacro(parts, args)}) }

  private def partsAsRawStringsMacro[P <: Tuple](parts: Expr[P])(using Quotes, Type[P]): Expr[Seq[String]] = {
    '{ ${parts}.productIterator.toSeq.map(_.asInstanceOf[String]) }
  }

  private def rawStringMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using q: Quotes, tpe: Type[P]): Expr[String] = {
    import q.reflect._

    val argsSeq: Seq[Expr[Any]] = args match {
      case Varargs(es) => es
    }
    val argsSeqString: Seq[Expr[String]] = argsSeq.map {
      case '{ $s: String } => s
      case '{ $f: SchematicConnectorLabel[?] } => '{ s"??${${f}.id}" }
      case '{ $f: SchematicFunctionLabel[?] | SchematicPredicateLabel[?] } => '{ s"?${${f}.id}" }
      case '{ $f: ConstantFunctionLabel[?] | ConstantPredicateLabel[?] | ConstantConnectorLabel[?] } => '{ s"${${f}.id}" }
      case '{ $other } => '{ ${other}.toString }
    }
    val partsSeq: Expr[Seq[String]] = '{ ${parts}.productIterator.toSeq.map(_.asInstanceOf[String]) }
    val argsSeqWithEmpty: Expr[Seq[String]] = argsSeqString.foldRight('{Seq("")})((e, acc) => '{ $e +: $acc })
    val exprString: Expr[String] = '{ ${partsSeq}.zip(${argsSeqWithEmpty}).flatMap { case (p, a) => Seq(p, a) }.reduce { case (l, r) => l + r } }

    exprString
  }

}
