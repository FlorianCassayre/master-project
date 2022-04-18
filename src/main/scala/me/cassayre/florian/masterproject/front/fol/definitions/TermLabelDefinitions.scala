package me.cassayre.florian.masterproject.front.fol.definitions

import scala.reflect.TypeTest

trait TermLabelDefinitions extends CommonDefinitions {

  sealed abstract class TermLabel extends Label

  final case class VariableLabel(id: String) extends TermLabel

  sealed abstract class FunctionLabel[N <: Arity] extends TermLabel with WithArity[N]
  final case class ConstantFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N]
  final case class SchematicFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N] with SchematicLabel

  object ConstantFunctionLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantFunctionLabel[N] = ConstantFunctionLabel(id, v.value)
    def unsafe(id: String, arity: Int): ConstantFunctionLabel[?] = ConstantFunctionLabel(id, arity)
  }

  object SchematicFunctionLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicFunctionLabel[N] = SchematicFunctionLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicFunctionLabel[?] = SchematicFunctionLabel(id, arity)
  }
  object SchematicFunctionLabel2 {
    def unapply[N <: Arity](f: SchematicFunctionLabel[N]): Option[(String, N)] = Some((f.id, f.arity))
  }

  given [N <: Arity](using v: ValueOf[N]): TypeTest[SchematicFunctionLabel[?], SchematicFunctionLabel[N]] with
    def unapply(f: SchematicFunctionLabel[?]): Option[f.type & SchematicFunctionLabel[N]] =
      if(f.arity == v.value) Some(f.asInstanceOf[f.type & SchematicFunctionLabel[N]]) else None

}
