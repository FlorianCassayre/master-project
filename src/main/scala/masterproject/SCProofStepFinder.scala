package masterproject

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.{SCProof, SCProofChecker}
import lisa.kernel.Printer

import scala.collection.View

/**
 * This module aims at reconstructing kernel proof steps using only the conclusion and the premises.
 */
object SCProofStepFinder {

  final case class NoProofStepFound(message: String) extends Exception(message)

  def findPossibleProofSteps(proof: SCProof, conclusion: Sequent, premises: Seq[Int] = Seq.empty): View[SCProofStep] = {
    require(premises.forall(i => proof.steps.indices.contains(i) || proof.imports.indices.contains(-(i + 1))))

    val checker = SCProofChecker.checkSingleSCStep
    val Sequent(left, right) = conclusion

    val SCProof(steps, _) = proof
    val searchedSteps = premises.map(i => (proof.getSequent(i), i))

    if (right.isEmpty) {
      // We know in advance that it's going to be impossible
      View.empty
    } else {
      val rightRefl = right.view.collect {
        case f@PredicateFormula(`equality`, Seq(l, r)) if isSame(l, r) => f
      }

      val viewRewrite: View[SCProofStep] = premises.distinct.view.filter(i => isSameSequent(conclusion, proof.getSequent(i))).map(Rewrite(conclusion, _))
      val viewHypothesis: View[SCProofStep] = left.view.filter(l => right.exists(r => isSameSet(Set(l), Set(r)))).map(Hypothesis(conclusion, _))
      val viewRightRefl: View[SCProofStep] = if(left.isEmpty && right.sizeIs == 1) rightRefl.map(RightRefl(conclusion, _)) else View.empty

      val viewOtherSteps: View[SCProofStep] = {
        if (searchedSteps.nonEmpty) { // The following steps require premises
          def collect[L <: FormulaLabel, A](f: PartialFunction[Formula, (L, A)])(formulas: Set[Formula]): Map[L, Set[A]] =
            formulas.collect(f).groupBy(_._1).view.mapValues(_.map(_._2)).toMap.withDefaultValue(Set.empty)

          val binaryConnectorCollector = collect { case f@ConnectorFormula(label, Seq(l, r)) => label -> (l, r) } _
          val (leftBinaryConnectors, rightBinaryConnectors) = (binaryConnectorCollector(left), binaryConnectorCollector(right))
          val binderCollector = collect { case f@BinderFormula(label, _, _) => label -> f } _
          val (leftBinders, rightBinders) = (binderCollector(left), binderCollector(right))
          val (leftNegConnectors, rightNegConnectors) =
            (left.collect { case f@ConnectorFormula(`Neg`, Seq(u)) => u }, right.collect { case f@ConnectorFormula(`Neg`, Seq(u)) => u })
          val leftEquals = left.collect { case f@PredicateFormula(`equality`, Seq(a, b)) => (a, b) }

          def collectExistsOneDef(s: Set[Formula]): View[(VariableLabel, Formula)] = s.view.collect {
            case BinderFormula(`Exists`, y, BinderFormula(`Forall`, x,
            ConnectorFormula(`Iff`, Seq(PredicateFormula(`equality`, Seq(VariableTerm(x1), VariableTerm(y1))), phi))
            )) if x == x1 && y == y1 => (x, phi)
          }

          // The order of the arguments matters.
          // `f1` contains the value of the pattern, whereas `f2` contains the pattern (`x`).
          def inverseInstantiation(f1: Formula, f2: Formula, x: Option[VariableLabel]): Option[Option[Term]] = (f1, f2) match {
            case (PredicateFormula(label1, args1), PredicateFormula(label2, args2)) if label1 == label2 && args1.sizeIs == args2.size =>
              args1.zip(args2).foldLeft(Some(None): Option[Option[Term]]) { case (opt, (a1, a2)) =>
                // TODO missing recursive exploration on predicates arguments!
                val opt2 = (a1, a2) match {
                  case (VariableTerm(vx), _) if x.contains(vx) => Some(Some(a2))
                  case _ => if (isSame(a1, a2)) Some(None) else None // We may safely check for equivalence here
                }
                for {
                  v1 <- opt
                  v2 <- opt2
                  if v1.zip(v2).forall(isSame(_, _))
                } yield v1.orElse(v2)
              }
            case (ConnectorFormula(label1, args1), ConnectorFormula(label2, args2)) if label1 == label2 && args1.sizeIs == args2.size =>
              args1.zip(args2).foldLeft(Some(None): Option[Option[Term]]) { case (opt, (a1, a2)) =>
                for {
                  v1 <- opt
                  v2 <- inverseInstantiation(a1, a2, x)
                  if v1.zip(v2).forall(isSame(_, _))
                } yield v1.orElse(v2)
              }
            case (BinderFormula(label1, bound1, inner1), BinderFormula(label2, bound2, inner2)) if label1 == label2 && bound1 == bound2 =>
              inverseInstantiation(inner1, inner2, x.filter(_ != label1)) // Important: if `label1` equals `x` then we cannot search for `x` anymore
            case _ => None // The formulas are not structurally equal
          }

          def inverseTermSubstitution(f: Formula, t: Term, l: SchematicFunctionLabel): Formula = f match {
            case PredicateFormula(label, args) =>
              def inverseTermSubstitution(term: Term): Term = term match {
                case _ if isSame(term, t) => FunctionTerm(l, Seq.empty)
                case VariableTerm(_) => term
                case FunctionTerm(label, args) => FunctionTerm(label, args.map(inverseTermSubstitution))
              }

              PredicateFormula(label, args.map(inverseTermSubstitution))
            case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(inverseTermSubstitution(_, t, l)))
            case BinderFormula(label, bound, inner) => if (VariableTerm(bound) != t) BinderFormula(label, bound, inverseTermSubstitution(inner, t, l)) else f // Avoid capturing bound variables
          }

          def inverseFormulaSubstitution(f: Formula, g: Formula, l: SchematicPredicateLabel): Formula = f match {
            case _ if isSame(f, g) => PredicateFormula(l, Seq.empty)
            case PredicateFormula(label, args) => f
            case ConnectorFormula(label, args) => ConnectorFormula(label, args.map(inverseFormulaSubstitution(_, g, l)))
            case BinderFormula(label, bound, inner) => BinderFormula(label, bound, inverseFormulaSubstitution(inner, g, l))
          }

          // An arbitrary schematic function and predicate for substitution rules
          val phi = SchematicFunctionLabel("f", 0)
          val psi = SchematicPredicateLabel("p", 0)

          // Rules with one premise

          val rules1: View[SCProofStep] = searchedSteps.view.flatMap { case (s, i) =>
            View(
              // Special rules
              View(Weakening(conclusion, i)),

              // Left rules
              leftBinaryConnectors(And).view.map((l, r) => LeftAnd(conclusion, i, l, r)),
              leftBinaryConnectors(Iff).view.map((l, r) => LeftIff(conclusion, i, l, r)),
              leftNegConnectors.view.map(u => LeftNot(conclusion, i, u)),
              leftBinders(Forall).view.flatMap(b =>
                s.left.view.flatMap(inverseInstantiation(b.inner, _, Some(b.bound)).flatten.map(t => LeftForall(conclusion, i, b.inner, b.bound, t)))
              ),
              leftBinders(Exists).view.map(b => LeftExists(conclusion, i, b.inner, b.bound)),
              collectExistsOneDef(s.left).map { case (x, phi) => LeftExistsOne(conclusion, i, phi, x) },

              s.left.view.map(f => LeftRefl(conclusion, i, f)),

              // Right rules
              rightBinaryConnectors(Or).view.map((l, r) => RightOr(conclusion, i, l, r)),
              rightBinaryConnectors(Implies).view.map((l, r) => RightImplies(conclusion, i, l, r)),
              rightNegConnectors.view.map(u => RightNot(conclusion, i, u)),

              rightBinders(Forall).view.map(b => RightForall(conclusion, i, b.inner, b.bound)),
              rightBinders(Exists).view.flatMap(b =>
                s.right.view.flatMap(inverseInstantiation(b.inner, _, Some(b.bound)).flatten.map(t => RightExists(conclusion, i, b.inner, b.bound, t)))
              ),
              collectExistsOneDef(s.right).map { case (x, phi) => RightExistsOne(conclusion, i, phi, x) },

              // Substitutions
              leftEquals.view.flatMap(pair => View(pair, pair.swap)).flatMap { case (ss, tt) =>
                View(
                  s.left.map(ts => LeftSubstEq(conclusion, i, ss, tt, inverseTermSubstitution(ts, ss, phi), phi)),
                  s.right.map(ts => RightSubstEq(conclusion, i, ss, tt, inverseTermSubstitution(ts, ss, phi), phi)),
                ).flatten
              },
              leftBinaryConnectors(Iff).view.flatMap(pair => View(pair, pair.swap)).flatMap { case (l, r) =>
                View(
                  s.left.map(g => LeftSubstIff(conclusion, i, l, r, inverseFormulaSubstitution(g, l, psi), psi)),
                  s.right.map(g => RightSubstIff(conclusion, i, l, r, inverseFormulaSubstitution(g, l, psi), psi)),
                ).flatten
              }
            ).flatten
          }

          // Rules with two premises

          val rules2: View[SCProofStep] = searchedSteps.view.flatMap { case (s1, i) => searchedSteps.view.flatMap { case (s2, j) =>
            View(
              // Cut rule
              for {
                f <- s1.right.view
                f2 <- s2.left.view
                if isSame(f, f2)
                if isSameSet(left + f, s1.left union s2.left)
                if isSameSet(right + f, s2.right union s1.right)
                if s2.left.contains(f) && s1.right.contains(f)
              } yield Cut(conclusion, i, j, f),

              // Left rules
              leftBinaryConnectors(Or).view.map { case (l, r) => LeftOr(conclusion, Seq(i, j), Seq(l, r)) }, // TODO arbitrary arity
              leftBinaryConnectors(Implies).view.map((l, r) => LeftImplies(conclusion, i, j, l, r)),

              // Right rules
              rightBinaryConnectors(And).view.map { case (l, r) => RightAnd(conclusion, Seq(i, j), Seq(l, r)) }, // TODO same here
              rightBinaryConnectors(Iff).view.map((l, r) => RightIff(conclusion, i, j, l, r)),
            ).flatten
          }
          }

          (rules1 ++ rules2).filter(step => checker(proof.steps.size, step, i => proof.getSequent(i), Some(proof.imports.size))._1)
        } else {
          View.empty
        }
      }

      // For performance reasons we start with the inexpensive steps first

      viewRewrite ++ viewHypothesis ++ viewRightRefl ++ viewOtherSteps
    }
  }

  /**
   * Attempts to create a new proof with the given conclusion.
   * This routine will concatenate at most one proof step to the existing proof.
   * If there exists several possible ways to build the proof, the routine will pick one of them.
   * Usually it will try to pick "the most general one", but it is not guaranteed (however it shouldn't matter).
   * An exception is raised the step cannot be found.
   * While the resulting proof should always be correct, it should no be trusted.
   *
   * @param proof      the existing proof
   * @param conclusion the new proof conclusion
   * @param premises   optional premises
   * @param filter     an optional filter on the steps found
   * @return a new proof with the given conclusion
   */
  def proofStepFinder(proof: SCProof, conclusion: Sequent, premises: Seq[Int] = Seq.empty, filter: SCProofStep => Boolean = _ => true): SCProof = {
    val candidates = findPossibleProofSteps(proof, conclusion, premises)
    candidates.find(filter) match {
      case Some(step) => proof.withNewSteps(IndexedSeq(step))
      case None => throw NoProofStepFound("")
    }
  }
}
