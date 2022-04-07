package me.cassayre.florian.masterproject.front.parser

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter

// Note: on Intellij you may want to disable syntax highlighting for this file
// ("File Types" => "Text" => "Ignored Files and Folders", add "FrontMacro.scala")

object FrontMacro {

  import scala.quoted.*

  extension (inline sc: StringContext)
    inline def term(inline args: Any*): Term = ${ termImpl('sc, 'args) }
    inline def formula(inline args: Any*): Formula = ${ formulaImpl('sc, 'args) }
    inline def sequent(inline args: Any*): Sequent = ${ sequentImpl('sc, 'args) }
    inline def partial(inline args: Any*): PartialSequent = ${ partialImpl('sc, 'args) }

  private def termImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using Quotes): Expr[Term] =
    '{ FrontReader.readTerm(${rawStringImpl(sc, args)}) }
  private def formulaImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using Quotes): Expr[Formula] =
    '{ FrontReader.readFormula(${rawStringImpl(sc, args)}) }
  private def sequentImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using Quotes): Expr[Sequent] =
    '{ FrontReader.readSequent(${rawStringImpl(sc, args)}) }
  private def partialImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using Quotes): Expr[PartialSequent] =
    '{ FrontReader.readPartialSequent(${rawStringImpl(sc, args)}) }


  private def rawStringImpl(sc: Expr[StringContext], args: Expr[Seq[Any]])(using q: Quotes): Expr[String] = {
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
    val partsSeq: Seq[Expr[String]] = sc match {
      case '{ StringContext($vs: _*) } =>
        vs match { case Varargs(es) => es }
    }
    val rawParts: Seq[String] = partsSeq.map(_.asTerm).map {
      case Literal(c: Constant) => c.value.toString
    }
    val argsSeqWithEmpty: Seq[Expr[String]] = argsSeqString :+ '{""}
    val allExprs: Seq[Expr[Any]] = rawParts.zip(argsSeqWithEmpty).flatMap { case (p: String, a: Expr[Any]) =>
      Seq(Expr(p), a)
    }
    val exprString: Expr[String] = allExprs.map(e => '{ ${e}.toString }).reduce {
      case (l: Expr[Any], r: Expr[Any]) => '{ $l + $r }
    }
    exprString
  }

}
