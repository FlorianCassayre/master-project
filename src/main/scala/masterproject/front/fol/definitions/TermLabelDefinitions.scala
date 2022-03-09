package masterproject.front.fol.definitions

import scala.compiletime.constValue

trait TermLabelDefinitions extends CommonDefinitions {

  sealed abstract class TermLabel extends Label

  final case class VariableLabel(id: String) extends TermLabel

  sealed abstract class FunctionLabel[N <: Arity] extends TermLabel with WithArity[N]
  final case class ConstantFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N]
  final case class SchematicFunctionLabel[N <: Arity] protected(id: String, arity: N) extends FunctionLabel[N] with SchematicLabel

  object ConstantFunctionLabel {
    inline def apply[N <: Arity](id: String): ConstantFunctionLabel[N] = ConstantFunctionLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): ConstantFunctionLabel[?] = ConstantFunctionLabel(id, arity)
  }

  object FunctionLabel {
    inline def apply[N <: Arity](id: String): SchematicFunctionLabel[N] = SchematicFunctionLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): SchematicFunctionLabel[?] = SchematicFunctionLabel(id, arity)
  }

}
