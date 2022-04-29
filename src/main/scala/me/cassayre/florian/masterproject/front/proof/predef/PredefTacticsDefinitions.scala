package me.cassayre.florian.masterproject.front.proof.predef

import lisa.kernel.proof.SCProof
import me.cassayre.florian.masterproject.front.fol.FOL.*
import me.cassayre.florian.masterproject.front.unification.Unifier.*
import lisa.kernel.proof.SequentCalculus.*
import proven.tactics.SimplePropositionalSolver
import me.cassayre.florian.masterproject.front.proof.state.ProofEnvironmentDefinitions

trait PredefTacticsDefinitions extends ProofEnvironmentDefinitions {

  @deprecated
  case object TacticSolver extends TacticGoalFunctional {
    import Notations.*

    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      val steps = SimplePropositionalSolver.solveSequent(proofGoal).steps
      Some((IndexedSeq.empty, () => steps))
    }
  }

  case class TacticRewritePartial(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(left.keySet.forall(proofGoal.left.indices.contains) && right.keySet.forall(proofGoal.right.indices.contains)) {
        val rewritten = Sequent(
          proofGoal.left.indices.map(i => left.getOrElse(i, proofGoal.left(i))),
          proofGoal.right.indices.map(i => right.getOrElse(i, proofGoal.right(i)))
        )
        if(isSameSequent(proofGoal, rewritten)) {
          Some((IndexedSeq(rewritten), () => IndexedSeq(Rewrite(rewritten, -1))))
        } else {
          None
        }
      } else {
        None
      }
    }
  }

  case class TacticRewriteSequent(rewritten: Sequent) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      if(isSameSequent(proofGoal, rewritten)) {
        Some((IndexedSeq(rewritten), () => IndexedSeq(Rewrite(proofGoal, -1))))
      } else {
        None
      }
    }
  }

  object TacticalRewrite {
    def apply(left: Map[Int, Formula] = Map.empty, right: Map[Int, Formula] = Map.empty): TacticRewritePartial =
      TacticRewritePartial(left, right)
    def apply(rewritten: Sequent): TacticRewriteSequent = TacticRewriteSequent(rewritten)
  }

  case class TacticInstantiateFunction(f: SchematicFunctionLabel[?], r: Term, args: Seq[VariableLabel]) extends TacticGoalFunctional {
    override def apply(proofGoal: Sequent): Option[(IndexedSeq[Sequent], ReconstructSteps)] = {
      ??? // TODO backwards
    }
  }

  extension (theorem: Theorem) {
    def apply(f: SchematicFunctionLabel[?], r: Term, args: Seq[SchematicFunctionLabel[0]]): Option[Theorem] = {
      val map: Seq[AssignedFunction] = Seq(AssignedFunction.unsafe(f, LambdaFunction.unsafe(args, r)))
      val replaced = Sequent(
        theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, functions = map)),
        theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, functions = map))
      )
      val scProof = SCProof(
        IndexedSeq(
          InstFunSchema(replaced, -1, Map(toKernel(f) -> LambdaFunction.unsafe(args, r)))
        ),
        IndexedSeq(sequentToKernel(theorem.sequent))
      )
      Some(theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem)))
    }
    def apply[N <: Arity](f: SchematicFunctionLabel[N], r: FillArgs[SchematicFunctionLabel[0], N] => Term): Theorem = {
      val (args, term) = fillTupleParameters(SchematicFunctionLabel.apply[0], f.arity, r)
      val argsSeq = args.toSeq
      apply(f, term, argsSeq).get // Never fails by assumption
    }
    def apply(f: SchematicFunctionLabel[0], r: Term): Theorem =
      apply[0](f, EmptyTuple => r)
    def apply(f: SchematicPredicateLabel[?], r: Formula, args: Seq[SchematicFunctionLabel[0]]): Option[Theorem] = {
      if(args.size == f.arity && args.distinct == args) {
        val map: Seq[AssignedPredicate] = Seq(AssignedPredicate.unsafe(f, LambdaPredicate.unsafe(args, r)))
        val replaced = Sequent(
          theorem.sequent.left.map(formula => instantiateFormulaSchemas(formula, predicates = map)),
          theorem.sequent.right.map(formula => instantiateFormulaSchemas(formula, predicates = map))
        )
        val scProof = SCProof(
          IndexedSeq(
            InstPredSchema(replaced, -1, Map(toKernel(f) -> LambdaPredicate.unsafe(args, r)))
          ),
          IndexedSeq(sequentToKernel(theorem.sequent))
        )
        Some(theorem.environment.mkTheorem(replaced, scProof, IndexedSeq(theorem)))
      } else {
        None
      }
    }
    def apply[N <: Arity](f: SchematicPredicateLabel[N], r: FillArgs[SchematicFunctionLabel[0], N] => Formula): Theorem = {
      val (args, formula) = fillTupleParameters(SchematicFunctionLabel.apply[0], f.arity, r)
      val argsSeq = args.toSeq
      apply(f, formula, argsSeq).get // ditto
    }
    def apply(f: SchematicPredicateLabel[0], r: Formula): Theorem =
      apply[0](f, EmptyTuple => r)

    def rewrite(rewritten: Sequent): Option[Theorem] =
      TacticRewriteSequent(theorem.sequent).apply(rewritten).map { case (_, reconstruct) =>
        val scProof = SCProof(reconstruct(), IndexedSeq(sequentToKernel(theorem.sequent)))
        theorem.environment.mkTheorem(rewritten, scProof, IndexedSeq(theorem))
      }
  }

}
