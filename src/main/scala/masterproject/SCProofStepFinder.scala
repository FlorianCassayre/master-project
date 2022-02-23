package masterproject

import lisa.kernel.fol.FOL._
import lisa.kernel.proof.SequentCalculus.*
import lisa.kernel.proof.{SCProof, SCProofChecker}
import lisa.kernel.Printer

import scala.collection.View

/**
 * The proof step finder module.
 */
object SCProofStepFinder {

  final case class NoProofStepFound(message: String) extends Exception(message)

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
   * @return a new proof with the given conclusion
   */
  def proofStepFinder(proof: SCProof, conclusion: Sequent, premises: Seq[Int] = Seq.empty): SCProof = {
    // In the future we might want to add a `strict` flag to allow the user to detect useless steps, oddly organized proofs, etc.

    require(premises.forall(i => proof.steps.indices.contains(i) || proof.imports.indices.contains(-(i + 1))))

    val checker = SCProofChecker.checkSingleSCStep
    val Sequent(left, right) = conclusion

    val SCProof(steps, _) = proof
    val searchedSteps = premises.map(i => (proof.getSequent(i), i))

    if (right.isEmpty) {
      throw NoProofStepFound("Cannot prove a right-empty sequent")
    }

    val rewritten = premises.distinct.find(i => isSameSequent(conclusion, proof.getSequent(i)))
    if (rewritten.nonEmpty) {
      if (rewritten.get < 0 || proof.getSequent(rewritten.get) != conclusion) {
        // We still need to rewrite the conclusion to match the desired conclusion
        proof.withNewSteps(IndexedSeq(Rewrite(conclusion, rewritten.get)))
      } else {
        // Trivial
        proof
      }
    } else {
      lazy val rightRefl = right.view.collect {
        case f@PredicateFormula(`equality`, Seq(l, r)) if isSame(l, r) => f
      }
      val step = {
        if (left.sizeIs == 1 && right.sizeIs == 1 && isSameSet(left, right)) {
          Hypothesis(conclusion, left.head)
        } else if (left.isEmpty && right.sizeIs == 1 && rightRefl.nonEmpty) {
          RightRefl(conclusion, rightRefl.head)
        } else if (searchedSteps.nonEmpty) { // The following steps require premises
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

          // A schematic function for substitution rules
          val phi = SchematicFunctionLabel("f", 0)
          val psi = SchematicPredicateLabel("p", 0)

          // Rules with one premise

          val rules1: View[SCProofStep] = searchedSteps.view.flatMap { case (s, i) =>
            View(
              // Left rules
              leftBinaryConnectors(And).view.map((l, r) => LeftAnd(conclusion, i, l, r)),
              leftBinaryConnectors(Iff).view.map((l, r) => LeftIff(conclusion, i, l, r)),
              leftNegConnectors.view.map(u => LeftNot(conclusion, i, u)),
              leftBinders(Forall).view.flatMap(b =>
                s.left.view.flatMap(inverseInstantiation(b.inner, _, Some(b.bound)).flatten.map(t => LeftForall(conclusion, i, b.inner, b.bound, t)))
              ),
              leftBinders(Exists).view.map(b => LeftExists(conclusion, i, b.inner, b.bound)),
              collectExistsOneDef(s.left).map { case (x, phi) => LeftExistsOne(conclusion, i, phi, x) },
              View(Weakening(conclusion, i)),

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
              View(Weakening(conclusion, i)),

              // Substitutions
              leftEquals.view.flatMap(pair => View(pair, pair.swap)).flatMap { case (ss, tt) =>
                s.left.flatMap(ts =>
                  View(
                    LeftSubstEq(conclusion, i, ss, tt, inverseTermSubstitution(ts, ss, phi), phi),
                    RightSubstEq(conclusion, i, ss, tt, inverseTermSubstitution(ts, ss, phi), phi)
                  )
                )
              },
              leftBinaryConnectors(Iff).view.flatMap(pair => View(pair, pair.swap)).flatMap { case (l, r) =>
                s.left.flatMap(g =>
                  View(
                    LeftSubstIff(conclusion, i, l, r, inverseFormulaSubstitution(g, l, psi), psi),
                    RightSubstIff(conclusion, i, l, r, inverseFormulaSubstitution(g, l, psi), psi),
                  )
                )
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

          (rules1 ++ rules2).find(step => checker(proof.steps.size, step, i => proof(i).bot, Some(proof.imports.size))._1) match {
            case Some(step) => step
            case None => throw NoProofStepFound("Cannot prove sequent")
          }
        } else {
          // This case is only here to provide a more helpful message
          throw NoProofStepFound("Cannot prove sequent; remark that the first step should not rely on any assumption")
        }
      }

      proof.withNewSteps(IndexedSeq(step))
    }
  }
}
