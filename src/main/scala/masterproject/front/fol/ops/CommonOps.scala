package masterproject.front.fol.ops

import masterproject.front.fol.definitions.CommonDefinitions

import scala.compiletime.ops.int.-

trait CommonOps {
  this: CommonDefinitions =>

  protected type FillTupleIter[T, N <: Arity] <: Tuple = N match {
    case 0 => EmptyTuple
    case _ => T *: FillTupleIter[T, N - 1]
  }

  type FillTuple[T, N <: Arity] = N match {
    case 1 => T
    case _ => FillTupleIter[T, N]
  }

  protected def tuple2seq[T, N <: Arity](any: FillTuple[T, N]): Seq[T] =
    any match {
      case tuple: Tuple => tuple.productIterator.toSeq.asInstanceOf[Seq[T]]
      case _ => Seq(any.asInstanceOf[T]) // Safe cast
    }

  def fillTuple[T, N <: Arity](n: N, f: Int => T): FillTuple[T, N] =
    if(n == 1)
      f(0).asInstanceOf[FillTuple[T, N]]
    else
      (0 until n).foldRight(EmptyTuple: Tuple)((i, acc) => f(i) *: acc).asInstanceOf[FillTuple[T, N]]

  extension [T, N <: Arity](tuple: FillTuple[T, N])
    def toSeq: Seq[T] = tuple2seq(tuple)

}
