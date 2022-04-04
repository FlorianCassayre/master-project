package me.cassayre.florian.masterproject.front.fol.ops

import me.cassayre.florian.masterproject.front.fol.definitions.CommonDefinitions

import scala.compiletime.ops.int.-

trait CommonOps {
  this: CommonDefinitions =>

  protected type FillTuple[T, N <: Arity] = N match {
    case 0 => EmptyTuple
    case _ => T *: FillTuple[T, N - 1]
  }

  type FillArgs[T, N <: Arity] = N match {
    case 1 => T
    case _ => FillTuple[T, N]
  }

  private[front] def fillTupleParameters[N <: Arity, T, U](name: String => T, n: N, f: FillArgs[T, N] => U, taken: Set[String] = Set.empty): (FillArgs[T, N], U) = {
    val newIds = LazyList.from(0).map(i => s"x$i").filter(!taken.contains(_)).take(n).toIndexedSeq
    val parameters = fillTuple[T, N](n, i => name(newIds(i)))
    (parameters, f(parameters))
  }

  protected def tuple2seq[T, N <: Arity](any: FillArgs[T, N]): Seq[T] =
    any match {
      case tuple: Tuple => tuple.productIterator.toSeq.asInstanceOf[Seq[T]]
      case _ => Seq(any.asInstanceOf[T]) // Safe cast
    }

  def fillTuple[T, N <: Arity](n: N, f: Int => T): FillArgs[T, N] =
    if(n == 1)
      f(0).asInstanceOf[FillArgs[T, N]]
    else
      (0 until n).foldRight(EmptyTuple: Tuple)((i, acc) => f(i) *: acc).asInstanceOf[FillArgs[T, N]]

  extension [T, N <: Arity](tuple: FillArgs[T, N])
    def toSeq: Seq[T] = tuple2seq(tuple)

}