package me.cassayre.florian.masterproject.front.fol.definitions

trait TermLabelDefinitions extends CommonDefinitions {

  /** @see [[lisa.kernel.fol.FOL.TermLabel]] */
  sealed abstract class TermLabel extends Label

  /** @see [[lisa.kernel.fol.FOL.VariableLabel]] */
  final case class VariableLabel(id: String) extends TermLabel

  /** @see [[lisa.kernel.fol.FOL.FunctionLabel]] */
  sealed abstract class FunctionLabel[N <: Arity] extends TermLabel with WithArity[N]
  /** @see [[lisa.kernel.fol.FOL.ConstantFunctionLabel]] */
  final case class ConstantFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N]
  /** @see [[lisa.kernel.fol.FOL.SchematicFunctionLabel]] */
  final case class SchematicFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N] with SchematicLabel

  object ConstantFunctionLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantFunctionLabel[N] = ConstantFunctionLabel(id, v.value)
    def unsafe(id: String, arity: Int): ConstantFunctionLabel[?] = ConstantFunctionLabel(id, arity)
  }

  object SchematicFunctionLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicFunctionLabel[N] = SchematicFunctionLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicFunctionLabel[?] = SchematicFunctionLabel(id, arity)
  }

}
