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

  enum Variable {
    val expr: Expr[Any]
    case FunctionLabelVariable(expr: Expr[FunctionLabel[?]], placeholder: SchematicFunctionLabel[?])
    case PredicateLabelVariable(expr: Expr[PredicateLabel[?]], placeholder: SchematicPredicateLabel[?])
    case ConnectorLabelVariable(expr: Expr[ConnectorLabel[?]], placeholder: SchematicConnectorLabel[?])
    case VariableLabelVariable(expr: Expr[VariableLabel], placeholder: VariableLabel)
    case TermVariable(expr: Expr[Term], placeholder: SchematicFunctionLabel[0])
    case FormulaVariable(expr: Expr[Formula], placeholder: SchematicPredicateLabel[0])
  }
  import Variable.*

  case class Interpolator(idsAndVariables: Seq[(String, Variable)], tokens: Seq[FrontToken]) {
    val variables: Seq[Variable] = idsAndVariables.map { case (_, variable) => variable }
    val map: Map[String, Variable] = idsAndVariables.toMap
  }

  private def toTokens[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Interpolator = {
    import quotes.reflect.*

    // throw new Error(s"illegal interpolation variable: ${TypeTree.of[other]}")
    // TypeTree[ConstantType(Constant({))]
    def evaluateParts[Q <: Tuple](scrutiny: Type[Q], acc: Seq[String]): Seq[String] = scrutiny match {
      case '[ EmptyTuple ] => acc
      case '[ head *: tail ] =>
        val string = TypeTree.of[head].tpe match {
          case ConstantType(cst) => cst.value.asInstanceOf[String] // Should always match and succeed
        }
        evaluateParts(Type.of[tail], string +: acc)
      }
    // `Type.of[P]` is equivalent to `summon[Type[P]]`
    val evaluatedParts: Seq[String] = evaluateParts(Type.of[P], Seq.empty).reverse

    val partsTokens: Seq[Seq[FrontToken]] = evaluatedParts.map(FrontLexer.lexingAscii(_)).map(_.init)
    val takenNames: Set[String] = partsTokens.flatten.collect {
      case FrontToken.Identifier(id) => id
      case FrontToken.SchematicIdentifier(id) => id
      case FrontToken.SchematicConnectorIdentifier(id) => id
    }.toSet

    val argsSeq: Seq[Expr[Any]] = args match {
      case Varargs(es) => es
    }

    // TODO raise warning when using infix notation

    def resolveArity[N <: Arity](expr: Expr[LabelType & WithArityType[N]])(using Type[N]): Int =
      TypeTree.of[N].tpe match {
        case ConstantType(cst) => cst.value.asInstanceOf[Int]
        case _ => report.errorAndAbort(s"loosely typed label variable, the arity must be known at compile time: ${Type.show[N]}", expr)
      }

    val idsAndVariables: Seq[(String, Variable)] = argsSeq.zipWithIndex.foldLeft((Seq.empty[(String, Variable)], takenNames)) { case ((acc, taken), (expr, i)) =>
      val id = {
        val base = s"x$i"
        if(taken.contains(base)) freshId(taken, base) else base
      }
      val variable = expr match {
        case '{ $label: FunctionLabel[n] } => FunctionLabelVariable(label, SchematicFunctionLabel.unsafe(id, resolveArity(label)))
        case '{ $label: PredicateLabel[n] } => PredicateLabelVariable(label, SchematicPredicateLabel.unsafe(id, resolveArity(label)))
        case '{ $label: ConnectorLabel[n] } => ConnectorLabelVariable(label, SchematicConnectorLabel.unsafe(id, resolveArity(label)))
        case '{ $label: VariableLabel } => VariableLabelVariable(label, VariableLabel(id))
        //case '{ $term: Term } => TermVariable(term)
        case '{ $formula: Formula } => FormulaVariable(formula, SchematicPredicateLabel(id, 0))
        case '{ $t: q } => report.errorAndAbort(s"unsupported variable type: ${Type.show[q]}", expr)
      }
      ((id, variable) +: acc, taken + id)
    }._1.reverse

    val variables = idsAndVariables.map { case (_, variable) => variable }

    val variablesTokens: Seq[FrontToken] = variables.map {
      case FunctionLabelVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case PredicateLabelVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case ConnectorLabelVariable(_, placeholder) => FrontToken.SchematicConnectorIdentifier(placeholder.id)
      case VariableLabelVariable(_, placeholder) => FrontToken.Identifier(placeholder.id)
      case TermVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
      case FormulaVariable(_, placeholder) => FrontToken.SchematicIdentifier(placeholder.id)
    }

    val tokens: Seq[FrontToken] = partsTokens.head ++ variablesTokens.zip(partsTokens.tail).flatMap { case (v, p) => v +: p } :+ FrontToken.End()

    Interpolator(idsAndVariables, tokens)
  }

  private def getRenaming(variables: Seq[Variable])(using Quotes):
  Expr[(
    Map[SchematicFunctionLabel[?], FunctionLabel[?]],
      Map[SchematicPredicateLabel[?], PredicateLabel[?]],
      Map[SchematicConnectorLabel[?], ConnectorLabel[?]],
      Map[VariableLabel, VariableLabel]
    )] = {
    import LiftFOL.{*, given}

    def substMap[T, U](seq: Seq[(Expr[T], Expr[U])])(using Quotes, Type[T], Type[U]): Expr[Map[T, U]] = {
      val list: Seq[Expr[(T, U)]] = seq.map { case (k, v) =>
        '{ $k -> $v }
      }
      '{ ${liftSeq(list)}.toMap }
    }

    val functionsMap: Expr[Map[SchematicFunctionLabel[?], FunctionLabel[?]]] = substMap(variables.collect {
      case FunctionLabelVariable(label, placeholder) =>
        Expr(placeholder) -> label
    })
    val predicatesMap: Expr[Map[SchematicPredicateLabel[?], PredicateLabel[?]]] = substMap(variables.collect {
      case PredicateLabelVariable(label, placeholder) =>
        Expr(placeholder) -> label
    })
    val connectorsMap: Expr[Map[SchematicConnectorLabel[?], ConnectorLabel[?]]] = substMap(variables.collect {
      case ConnectorLabelVariable(label, placeholder) =>
        Expr(placeholder) -> label
    })
    val variablesMap: Expr[Map[VariableLabel, VariableLabel]] = substMap(variables.collect {
      case VariableLabelVariable(label, placeholder) =>
        Expr(placeholder) -> label
    })

    '{ ($functionsMap, $predicatesMap, $connectorsMap, $variablesMap) }
  }

  private def typeCheck(
    interpolator: Interpolator,
    functions: Set[SchematicFunctionLabel[?]],
    predicates: Set[SchematicPredicateLabel[?]],
    connectors: Set[SchematicConnectorLabel[?]],
    variables: Set[VariableLabel],
  )(using Quotes): Unit = {
    import quotes.reflect.*

    def reportArityMismatch(expr: Expr[?], expected: Int, actual: Int): Nothing =
      report.errorAndAbort(s"arity mismatch: variable label expects $expected arguments but you provided $actual", expr)

    // Either function or predicate
    functions.flatMap(f => interpolator.map.get(f.id).map(f -> _)).foreach { case (f, variable) =>
      variable match {
        case FunctionLabelVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            reportArityMismatch(label, placeholder.arity, f.arity)
          }
        case TermVariable(label, placeholder) =>
          if(f.arity != placeholder.arity) {
            report.errorAndAbort(s"variable term does not expect any arguments", label)
          }
        case other => report.errorAndAbort(s"expected term, got formula", other.expr)
      }
    }
  }


  private def termApplyMacro[P <: Tuple](parts: Expr[P], args: Expr[Seq[Any]])(using Quotes, Type[P]): Expr[Term] = {
    import quotes.reflect.*

    val interpolator = toTokens(parts, args)

    val resolved = FrontResolver.resolveTerm(FrontParser.parseTermOrFormula(interpolator.tokens))

    typeCheck(interpolator, schematicFunctionsOf(resolved), Set.empty, Set.empty, Set.empty)

    import LiftFOL.{*, given}

    val resolvedExpr = Expr(resolved)

    '{
      val (functionsMap, predicatesMap, connectorsMap, variablesMap) = ${getRenaming(interpolator.variables)}
      renameSchemas($resolvedExpr, functionsMap, variablesMap)
    }
  }
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

  private object LiftFOL {
    def liftSeq[T](seq: Seq[Expr[T]])(using Quotes, Type[T]): Expr[Seq[T]] =
      seq.foldRight('{ Seq.empty[T] })((e, acc) => '{ $e +: $acc })

    given ToExpr[SchematicFunctionLabel[?]] with
      def apply(f: SchematicFunctionLabel[?])(using Quotes): Expr[SchematicFunctionLabel[?]] =
        '{ SchematicFunctionLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    given ToExpr[ConstantFunctionLabel[?]] with
      def apply(f: ConstantFunctionLabel[?])(using Quotes): Expr[ConstantFunctionLabel[?]] =
        '{ ConstantFunctionLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    given ToExpr[SchematicPredicateLabel[?]] with
      def apply(f: SchematicPredicateLabel[?])(using Quotes) =
        '{ SchematicPredicateLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    given ToExpr[ConstantPredicateLabel[?]] with
      def apply(f: ConstantPredicateLabel[?])(using Quotes): Expr[ConstantPredicateLabel[?]] =
        '{ ConstantPredicateLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    given ToExpr[SchematicConnectorLabel[?]] with
      def apply(f: SchematicConnectorLabel[?])(using Quotes) =
        '{ SchematicConnectorLabel.unsafe(${Expr(f.id)}, ${Expr(f.arity.asInstanceOf[Int])}) }
    given ToExpr[VariableLabel] with
      def apply(l: VariableLabel)(using Quotes) =
        '{ VariableLabel(${Expr(l.id)}) }
    given ToExpr[BinderLabel] with
      def apply(l: BinderLabel)(using Quotes) =
        '{ BinderLabel(${Expr(l.id)}) }

    given ToExpr[FunctionLabel[?]] with
      def apply(f: FunctionLabel[?])(using Quotes): Expr[FunctionLabel[?]] = f match {
        case constant: ConstantFunctionLabel[?] => Expr(constant)(using summon[ToExpr[ConstantFunctionLabel[?]]])
        case schematic: SchematicFunctionLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicFunctionLabel[?]]])
      }
    given ToExpr[PredicateLabel[?]] with
      def apply(f: PredicateLabel[?])(using Quotes): Expr[PredicateLabel[?]] = f match {
        case constant: ConstantPredicateLabel[?] => Expr(constant)(using summon[ToExpr[ConstantPredicateLabel[?]]])
        case schematic: SchematicPredicateLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicPredicateLabel[?]]])
      }
    given ToExpr[ConnectorLabel[?]] with
      def apply(f: ConnectorLabel[?])(using Quotes): Expr[ConnectorLabel[?]] = f match {
        case constant: ConstantConnectorLabel[?] => ??? // Expr(constant)(using summon[ToExpr[ConstantConnectorLabel[?]]])
        case schematic: SchematicConnectorLabel[?] => Expr(schematic)(using summon[ToExpr[SchematicConnectorLabel[?]]])
      }

    given ToExpr[Term] with
      def apply(t: Term)(using Quotes): Expr[Term] = t match {
        case VariableTerm(label) => '{ VariableTerm(${Expr(label)}) }
        case FunctionTerm(label, args) => '{ FunctionTerm(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
      }
    given ToExpr[Formula] with
      def apply(f: Formula)(using Quotes): Expr[Formula] = f match {
        case PredicateFormula(label, args) => '{ PredicateFormula(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
        case ConnectorFormula(label, args) => '{ ConnectorFormula(${Expr(label)}, ${liftSeq(args.map(Expr.apply(_)))}) }
        case BinderFormula(label, bound, inner) => '{ BinderFormula(${Expr(label)}, ${Expr(bound)}, ${Expr(inner)}) }
      }
  }

}
