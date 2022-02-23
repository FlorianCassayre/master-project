package masterproject

import lisa.kernel.fol.FOL.*
import lisa.KernelHelpers.*
import lisa.kernel.proof.SCProof
import lisa.kernel.proof.SequentCalculus.*
import masterproject.SCProofBuilder.*

/**
 * A proof builder, a monad that provides an alternative way of organizing proofs using for-comprehensions.
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
  // Sadly this method is required in Scala 2 if we want to destructure the tuples
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

  def get: MonadicSCProofBuilder[SCProof] = MonadicSCProofBuilder(s => (s, s))
  def gets[A](f: SCProof => A): MonadicSCProofBuilder[A] = MonadicSCProofBuilder(s => (s, f(s)))
  private def put(s: SCProof): MonadicSCProofBuilder[Unit] = MonadicSCProofBuilder(_ => (s, ()))
  def modify(ss: SCProof => SCProof): MonadicSCProofBuilder[(Sequent, Int)] = for {s <- get; _ <- put(ss(s)); p <- get} yield (p.conclusion, p.steps.size - 1)
  def append(step: SCProofStep): MonadicSCProofBuilder[(Sequent, Int)] = for (t <- modify(p => p.withNewSteps(IndexedSeq(step)))) yield t
  def append(anyStep: SCAnyProofStep): MonadicSCProofBuilder[(Sequent, Int)] =
    for (t <- modify(p => {
      val newImports = p.imports ++ anyStep.imports.filter(imprt => !p.imports.exists(isSameSequent(imprt, _)))
      // This must always succeed:
      val usedImportsIndices = anyStep.imports.map(imprt => newImports.zipWithIndex.find { case (otherImports, _) => isSameSequent(imprt, otherImports) }.get._2)
      SCProofStepFinder.proofStepFinder(p.copy(imports = newImports), anyStep.conclusion, anyStep.premises ++ usedImportsIndices.map(i => -(i + 1)))
    })) yield t
  def append(sequent: Sequent): MonadicSCProofBuilder[(Sequent, Int)] = append(SCAnyProofStep(sequent, Seq.empty, Seq.empty))
  def subproof(builder: MonadicSCProofBuilder[Unit], display: Boolean = true): MonadicSCProofBuilder[(Sequent, Int)] = {
    val sp = create(builder)
    for {
      t <- modify { p =>
        val newImports = p.imports ++ (sp.imports.diff(p.imports))
        p.copy(imports = newImports).withNewSteps(IndexedSeq(SCSubproof(sp, sp.imports.map(imprt => -(newImports.indexOf(imprt) + 1)), display)))
      }
    } yield t
  }
  def create(builder: MonadicSCProofBuilder[Unit]): SCProof = builder.execState(SCProof())

  implicit def sequentToProofBuilder(sequent: Sequent): MonadicSCProofBuilder[(Sequent, Int)] = append(sequent)
  implicit def anyStepToProofBuilder(anyStep: SCAnyProofStep): MonadicSCProofBuilder[(Sequent, Int)] = append(anyStep)
  implicit def proofStepToProofBuilder(step: SCProofStep): MonadicSCProofBuilder[(Sequent, Int)] = append(step)
  implicit def proofModifyToProofBuilder(f: SCProof => SCProof): MonadicSCProofBuilder[(Sequent, Int)] = modify(f)
}
