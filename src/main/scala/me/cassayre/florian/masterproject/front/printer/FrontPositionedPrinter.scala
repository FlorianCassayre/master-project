package me.cassayre.florian.masterproject.front.printer

import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.proof.Proof.*
import me.cassayre.florian.masterproject.front.theory.SetTheory
import me.cassayre.florian.masterproject.front.printer.FrontPrintNode.*

/**
 * A set of methods to positioned-print kernel trees.
 */
object FrontPositionedPrinter {

  private def mkSep(items: FrontPrintNode*)(separator: FrontLeaf): IndexedSeq[FrontPrintNode] = {
    val nodes = items match {
      case head +: tail =>
        head +: tail.flatMap(Seq(separator, _))
      case other => other
    }
    nodes.toIndexedSeq
  }

  private def spaceSeparator(compact: Boolean): String = if(compact) "" else " "
  private def commaSeparator(compact: Boolean, symbol: String = ","): String = s"$symbol${spaceSeparator(compact)}"

  private def positionedParentheses(content: FrontPrintNode): IndexedSeq[FrontPrintNode] = IndexedSeq("(", content, ")")

  private def positionedFunction(name: String, args: Seq[FrontBranch], compact: Boolean, dropParentheses: Boolean = true): FrontBranch = {
    if(dropParentheses && args.isEmpty) FrontBranch(name) else FrontBranch(FrontLeaf(s"$name(") +: mkSep(args: _*)(commaSeparator(compact)) :+ FrontLeaf(")"))
  }

  private def positionedInfix(operator: String, left: FrontPrintNode, right: FrontPrintNode, compact: Boolean): FrontBranch =
    FrontBranch(mkSep(left, operator, right)(spaceSeparator(compact)))
  private def positionedInfix(operator: FrontPrintNode, left: IndexedSeq[FrontPrintNode], right: IndexedSeq[FrontPrintNode], compact: Boolean): FrontBranch =
    FrontBranch(mkSep((left ++ IndexedSeq(operator) ++ right): _*)(spaceSeparator(compact)))

  // Special symbols that aren't defined in this theory
  private val (membership, subsetOf, sameCardinality) = (
    SetTheory.membership,
    SetTheory.subset,
    SetTheory.sameCardinality
  )
  private val (emptySet, unorderedPair, orderedPair, singleton, powerSet, unionSet) = (
    SetTheory.emptySet,
    SetTheory.unorderedPairSet,
    ConstantFunctionLabel("ordered_pair", 2),
    SetTheory.singletonSet,
    SetTheory.powerSet,
    SetTheory.unionSet,
  )
  private val nonAtomicPredicates = Set[PredicateLabel[?]](equality, membership, subsetOf, sameCardinality) // Predicates which require parentheses (for readability)

  private def positionedFormulaInternal(formula: Formula, isRightMost: Boolean, compact: Boolean): FrontBranch = formula match {
    case PredicateFormula(label, args) => label match {
      case `equality` => args match {
        case Seq(l, r) => positionedInfix(label.id, positionedTerm(l), positionedTerm(r), compact)
        case _ => throw new Exception
      }
      case `membership` => args match {
        case Seq(l, r) => positionedInfix("∈", positionedTerm(l), positionedTerm(r), compact)
        case _ => throw new Exception
      }
      case `subsetOf` => args match {
        case Seq(l, r) => positionedInfix("⊆", positionedTerm(l), positionedTerm(r), compact)
        case _ => throw new Exception
      }
      case `sameCardinality` => args match {
        case Seq(l, r) => positionedInfix("~", positionedTerm(l), positionedTerm(r), compact)
        case _ => throw new Exception
      }
      case _ =>
        val labelString = label match {
          case ConstantPredicateLabel(id, _) => id
          case SchematicPredicateLabel(id, _) => s"?$id"
        }
        positionedFunction(labelString, args.map(positionedTerm(_, compact)), compact)
    }
    case ConnectorFormula(label, args) =>
      (label, args) match {
        case (`neg`, Seq(arg)) =>
          val isAtomic = arg match {
            case PredicateFormula(label, _) => !nonAtomicPredicates.contains(label)
            case ConnectorFormula(`neg`, _) => true
            case _ => false
          }
          val bodyString = positionedFormulaInternal(arg, isRightMost, compact)
          val bodyParenthesized = if(isAtomic) IndexedSeq(bodyString) else positionedParentheses(bodyString)
          FrontBranch(FrontLeaf(label.id) +: bodyParenthesized)
        case (binary @ (`implies` | `iff` | `and` | `or`), Seq(l, r)) =>
          val precedences: Map[ConnectorLabel[?], Int] = Map(
            and -> 1,
            or -> 2,
            implies -> 3,
            iff -> 4,
          )
          val precedence = precedences(binary)
          val isLeftParentheses = l match {
            case _: BinderFormula => true
            case PredicateFormula(leftLabel, _) => nonAtomicPredicates.contains(leftLabel)
            case ConnectorFormula(leftLabel, _) => precedences.get(leftLabel).exists(_ >= precedence)
          }
          val isRightParentheses = r match {
            case _: BinderFormula => !isRightMost
            case PredicateFormula(leftLabel, _) => nonAtomicPredicates.contains(leftLabel)
            case ConnectorFormula(rightLabel, _) => precedences.get(rightLabel).exists(_ > precedence)
          }
          val (leftString, rightString) = (positionedFormulaInternal(l, isLeftParentheses, compact), positionedFormulaInternal(r, isRightMost || isRightParentheses, compact))
          val leftParenthesized = if(isLeftParentheses) positionedParentheses(leftString) else IndexedSeq(leftString)
          val rightParenthesized = if(isRightParentheses) positionedParentheses(rightString) else IndexedSeq(rightString)
          positionedInfix(label.id, leftParenthesized, rightParenthesized, compact)
        case (nary @ (`and` | `or`), args) if args.nonEmpty =>
          // FIXME wrong indexing if we do that
          // Rewriting to match the above case; namely op(a) --> a, and op(a, ...rest) --> op(a, op(...rest))
          // Empty args aren't allowed here
          // Invariant: args.size > 2
          if(args.sizeIs == 1) {
            positionedFormulaInternal(args.head, isRightMost, compact)
          } else {
            positionedFormulaInternal(ConnectorFormula(nary, Seq(args.head, ConnectorFormula(nary, args.tail))), isRightMost, compact)
          }
        case _ => positionedFunction(label.id, args.map(a => positionedFormulaInternal(a, isRightMost, compact)), compact)
      }
    case BinderFormula(label, bound, inner) =>
      def accumulateNested(f: Formula, acc: Seq[VariableLabel]): (Seq[VariableLabel], Formula) = f match {
        case BinderFormula(`label`, nestBound, nestInner) => accumulateNested(nestInner, nestBound +: acc)
        case _ => (acc, f)
      }
      val (bounds, innerNested) = accumulateNested(inner, Seq(bound))

      val innerTree = FrontBranch(mkSep(
        FrontLeaf(s"${label.id}${bounds.reverse.map(_.id).mkString(commaSeparator(compact))}."),
        positionedFormulaInternal(innerNested, true, compact),
      )(spaceSeparator(compact)))
      bounds.tail.foldLeft(innerTree)((acc, _) => FrontBranch(acc))
  }

  /**
   * Returns a string representation of this formula. See also [[positionedTerm]].
   * Example output:
   * <pre>
   * ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
   * </pre>
   * @param formula the formula
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this formula
   */
  def positionedFormula(formula: Formula, compact: Boolean = false): FrontBranch = {
    val f = positionedFormulaInternal(formula, true, compact)
    val freeVariables = formula.freeVariables
    if(freeVariables.nonEmpty)
      FrontBranch(mkSep((s"\\${freeVariables.map(_.id).mkString(commaSeparator(compact))}." +: f.children): _*)(spaceSeparator(compact)))
    else
      f
  }

  def prettyFormula(formula: Formula, compact: Boolean = false): String =
    positionedFormula(formula, compact).print

  /**
   * Returns a string representation of this term. See also [[positionedFormula]].
   * Example output:
   * <pre>
   * f({w, (x, y)}, z)
   * </pre>
   * @param term the term
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this term
   */
  def positionedTerm(term: Term, compact: Boolean = false): FrontBranch = term match {
    case VariableTerm(label) => FrontBranch(label.id)
    case FunctionTerm(label, args) =>
      label match {
        case `emptySet` => args match {
          case Seq() => positionedFunction("∅", Seq.empty, compact, dropParentheses = true)
          case _ => throw new Exception
        }
        case `unorderedPair` => args match {
          case Seq(l, r) => FrontBranch("{", positionedTerm(l, compact), commaSeparator(compact), positionedTerm(r, compact), "}")
          case _ => throw new Exception
        }
        case `orderedPair` => args match {
          case Seq(l, r) => FrontBranch("(", positionedTerm(l, compact), commaSeparator(compact), positionedTerm(r, compact), ")")
          case _ => throw new Exception
        }
        case `singleton` => args match {
          case Seq(s) => FrontBranch("{", positionedTerm(s, compact), "}")
          case _ => throw new Exception
        }
        case `powerSet` => args match {
          case Seq(s) => positionedFunction("P", Seq(positionedTerm(s, compact)), compact)
          case _ => throw new Exception
        }
        case `unionSet` => args match {
          case Seq(s) => positionedFunction("U", Seq(positionedTerm(s, compact)), compact)
          case _ => throw new Exception
        }
        case _ =>
          val labelString = label match {
            case ConstantFunctionLabel(id, _) => id
            case SchematicFunctionLabel(id, _) => s"?$id"
          }
          positionedFunction(labelString, args.map(positionedTerm(_, compact)), compact)
      }
  }

  def prettyTerm(term: Term, compact: Boolean = false): String =
    positionedTerm(term, compact).print


    /**
   * Returns a string representation of this sequent.
   * Example output:
   * <pre>
   * ⊢ ∀x, y. (∀z. (z ∈ x) ↔ (z ∈ y)) ↔ (x = y)
   * </pre>
   * @param sequent the sequent
   * @param compact whether spaces should be omitted between tokens
   * @return the string representation of this sequent
   */
  def positionedSequent(sequent: Sequent, compact: Boolean = false): FrontBranch = {
    def positionedFormulas(seq: IndexedSeq[Formula]): IndexedSeq[FrontPrintNode] =
      mkSep(seq.map(positionedFormula(_, compact)).sortBy(_.print): _*)(commaSeparator(compact, ";"))
    FrontBranch(mkSep((positionedFormulas(sequent.left) ++ Seq(FrontLeaf("⊢")) ++ positionedFormulas(sequent.right)): _*)(spaceSeparator(compact)))
  }

  def prettySequent(sequent: Sequent, compact: Boolean = false): String =
    positionedSequent(sequent, compact).print

}
