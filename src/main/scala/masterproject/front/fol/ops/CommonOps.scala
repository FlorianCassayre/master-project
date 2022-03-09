package masterproject.front.fol.ops

import masterproject.front.fol.definitions.CommonDefinitions

import scala.compiletime.ops.int.-

trait CommonOps {
  this: CommonDefinitions =>

  protected type FillTupleIter[T, N <: Arity] <: Tuple = N match {
    case 0 => EmptyTuple
    case _ => T *: FillTupleIter[T, N - 1]
  }

  protected type FillTuple[T, N <: Arity] = N match {
    case 1 => T | FillTupleIter[T, N]
    case _ => FillTupleIter[T, N]
  }

  protected def tuple2seq[T, N <: Arity](any: FillTuple[T, N]): Seq[T] =
    any match {
      case tuple: Tuple => tuple.productIterator.toSeq.asInstanceOf[Seq[T]]
      case _ => Seq(any.asInstanceOf[T]) // Safe cast
    }

}
