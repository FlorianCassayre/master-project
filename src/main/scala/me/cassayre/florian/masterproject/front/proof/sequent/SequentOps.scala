package me.cassayre.florian.masterproject.front.proof.sequent

import me.cassayre.florian.masterproject.front.proof.sequent.SequentDefinitions
import me.cassayre.florian.masterproject.front.fol.FOL.*

trait SequentOps extends SequentDefinitions {

  protected trait IndexedSeqConverter[S, T] {
    def apply(t: T): IndexedSeq[S]
  }

  given[S]: IndexedSeqConverter[S, Unit] with {
    override def apply(u: Unit): IndexedSeq[S] = IndexedSeq.empty
  }
  given[S]: IndexedSeqConverter[S, EmptyTuple] with {
    override def apply(t: EmptyTuple): IndexedSeq[S] = IndexedSeq.empty
  }
  given[S, H <: S, T <: Tuple, C1] (using converter: IndexedSeqConverter[S, T]): IndexedSeqConverter[S, H *: T] with {
    override def apply(t: H *: T): IndexedSeq[S] = t.head +: converter(t.tail)
  }
  given givenTupleValueConversion[S, H, T <: Tuple, C1] (using tupleConverter: IndexedSeqConverter[S, T], valueConverter: Conversion[H, S]): IndexedSeqConverter[S, H *: T] with {
    override def apply(t: H *: T): IndexedSeq[S] = valueConverter(t.head) +: tupleConverter(t.tail)
  }
  given[S, T <: S]: IndexedSeqConverter[S, T] with {
    override def apply(f: T): IndexedSeq[S] = IndexedSeq(f)
  }
  given givenValueConversion[S, T](using converter: Conversion[T, S]): IndexedSeqConverter[S, T] with {
    override def apply(f: T): IndexedSeq[S] = IndexedSeq(f: S)
  }
  given[S, I <: Iterable[S]]: IndexedSeqConverter[S, I] with {
    override def apply(s: I): IndexedSeq[S] = s.toIndexedSeq
  }

  protected def any2set[S, A, T <: A](any: T)(using converter: IndexedSeqConverter[S, T]): IndexedSeq[S] = converter(any)

  extension[A, T1 <: A] (left: T1)(using IndexedSeqConverter[Formula, T1]) {
    infix def |-[B, T2 <: B](right: T2)(using IndexedSeqConverter[Formula, T2]): Sequent = Sequent(any2set(left), any2set(right))
  }

  object |- {
    def unapply(left: IndexedSeq[Formula], right: IndexedSeq[Formula]): Option[Sequent] =
      Some(Sequent(left, right))
  }

  type KernelSequent = lisa.kernel.proof.SequentCalculus.Sequent
  extension (s: KernelSequent) {
    infix def +<(f: Formula): KernelSequent = s.copy(left = s.left + f)
    infix def -<(f: Formula): KernelSequent = s.copy(left = s.left - f)
    infix def +>(f: Formula): KernelSequent = s.copy(right = s.right + f)
    infix def ->(f: Formula): KernelSequent = s.copy(right = s.right - f)
  }

}
