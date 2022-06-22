package me.cassayre.florian.masterproject.util

import lisa.kernel.fol.FOL.*
import utilities.Helpers.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import me.cassayre.florian.masterproject.util.SCProofBuilder.{*, given}

/**
 * A proof builder, a monad that provides an alternative way of organizing proofs using for-comprehensions.
 * Is an interface for [[SCProofBuilder]].
 * @tparam A the result type
 */
case class MonadicSCProofBuilder[A] private(private val run: SCProof => (SCProof, A)) {
  private def execState(s: SCProof): SCProof = run(s)._1
  def map[B](ab: A => B): MonadicSCProofBuilder[B] =
    MonadicSCProofBuilder(s => run(s) match {
      case (s, a) => (s, ab(a))
    })
  def flatMap[B](afb: A => MonadicSCProofBuilder[B]): MonadicSCProofBuilder[B] =
    MonadicSCProofBuilder(s => run(s) match {
      case (s, a) => afb(a).run(s)
    })
  // Sadly this method is required in Scala 2 & 3 if we want to destructure the tuples
  // Nevertheless we still include a runtime check to prevent filtering
  def withFilter(f: A => Boolean): MonadicSCProofBuilder[A] =
    MonadicSCProofBuilder(s => run(s) match {
      case t @ (_, a) =>
        assert(f(a))
        t
    })
}

/**
 * The API to create and update proof builders.
 */
object MonadicSCProofBuilder {
  type LastStep = (Sequent, Int)

  /**
   * Obtains the current state of the proof that is getting built.
   * @return the builder with the proof as a result
   */
  def get: MonadicSCProofBuilder[SCProof] = MonadicSCProofBuilder(s => (s, s))

  /**
   * Obtains some property of the proof that is getting build.
   * @param f the property to extract
   * @tparam A the type of the property to be extracted
   * @return the builder with that property as a result
   */
  def gets[A](f: SCProof => A): MonadicSCProofBuilder[A] = MonadicSCProofBuilder(s => (s, f(s)))
  private def put(s: SCProof): MonadicSCProofBuilder[Unit] = MonadicSCProofBuilder(_ => (s, ()))
  /**
   * Modifies the proof in a non-standard way (e.g. dynamic tactic).
   * @param ss the modification function
   * @return the builder with the last step as a result
   */
  def modify(ss: SCProof => SCProof): MonadicSCProofBuilder[LastStep] = for {s <- get; _ <- put(ss(s)); p <- get} yield (p.conclusion, p.steps.size - 1)
  /**
   * Appends a kernel proof step to the proof.
   * @param step the step to be appended
   * @return the builder with that step as a result
   */
  def append(step: SCProofStep): MonadicSCProofBuilder[LastStep] = for (t <- modify(p => p.withNewSteps(IndexedSeq(step)))) yield t
  /**
   * Appends a higher-level proof step to the proof.
   * @param anyStep the step to be appended
   * @return the builder with that step as a result
   */
  def append(anyStep: SCImplicitProofStep): MonadicSCProofBuilder[LastStep] =
    for (t <- modify(p => {
      val newImports = p.imports ++ anyStep.imports.filter(imprt => !p.imports.exists(isSameSequent(imprt, _)))
      // This must always succeed:
      val usedImportsIndices = anyStep.imports.map(imprt => newImports.zipWithIndex.find { case (otherImports, _) => isSameSequent(imprt, otherImports) }.get._2)
      SCProofStepFinder.proofStepFinder(p.copy(imports = newImports), anyStep.conclusion, anyStep.premises ++ usedImportsIndices.map(i => -(i + 1))).get
    })) yield t
  /**
   * Appends a sequent to the proof. This sequent is automatically converted into an [[SCImplicitProofStep]] with default arguments.
   * @param sequent the sequent corresponding to the conclusion
   * @return the builder with that step as a result
   */
  def append(sequent: Sequent): MonadicSCProofBuilder[LastStep] = append(SCImplicitProofStep(sequent, Seq.empty, Seq.empty))
  /**
   * Starts a new subproof within that proof. Note that as an implementation limitation, it is not possible to refer to
   * steps outside of this scope.
   * @param builder a builder representing the subproof
   * @param display whether this subproof should be displayed or not
   * @return the builder with that step as a result
   */
  def subproof(builder: MonadicSCProofBuilder[Unit], display: Boolean = true): MonadicSCProofBuilder[LastStep] = {
    val sp = create(builder)
    for {
      t <- modify { p =>
        val newImports = p.imports ++ sp.imports.diff(p.imports)
        p.copy(imports = newImports).withNewSteps(IndexedSeq(SCSubproof(sp, sp.imports.map(imprt => -(newImports.indexOf(imprt) + 1)), display)))
      }
    } yield t
  }
  /**
   * Appends a new subproof within that proof. This method is only here to mitigate the implementation limitation.
   * @param proof the proof to be added as a subproof
   * @param display whether this subproof should be displayed or not
   * @return the builder with that step as a result
   */
  def subproof(proof: SCProof, display: Boolean): MonadicSCProofBuilder[LastStep] = subproof(for (_ <- put(proof); r <- modify(identity)) yield (), display)
  /**
   * Creates the proof.
   * @param builder the builder for which the proof should be created
   * @return the proof built by that builder
   */
  def create(builder: MonadicSCProofBuilder[Unit]): SCProof = builder.execState(SCProof())

  given Conversion[Sequent, MonadicSCProofBuilder[LastStep]] = append
  given Conversion[SCImplicitProofStep, MonadicSCProofBuilder[LastStep]] = append
  given Conversion[SCProofStep, MonadicSCProofBuilder[LastStep]] = append
  given Conversion[SCProof => SCProof, MonadicSCProofBuilder[LastStep]] = modify
}
