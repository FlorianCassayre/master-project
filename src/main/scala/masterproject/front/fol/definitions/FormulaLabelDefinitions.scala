package masterproject.front.fol.definitions

import scala.compiletime.constValue

trait FormulaLabelDefinitions extends CommonDefinitions {

  sealed abstract class FormulaLabel extends Label

  sealed abstract class PredicateLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  final case class ConstantPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N]
  final case class SchematicPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N] with SchematicLabel

  object ConstantPredicateLabel {
    inline def apply[N <: Arity](id: String): ConstantPredicateLabel[N] = ConstantPredicateLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): ConstantPredicateLabel[?] = ConstantPredicateLabel(id, arity)
  }
  object SchematicPredicateLabel {
    inline def apply[N <: Arity](id: String): SchematicPredicateLabel[N] = SchematicPredicateLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): SchematicPredicateLabel[?] = SchematicPredicateLabel(id, arity)
  }

  val equality: ConstantPredicateLabel[2] = ConstantPredicateLabel("=")

  sealed abstract class ConnectorLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  final case class ConstantConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N]
  final case class SchematicConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N] with SchematicLabel

  object ConstantConnectorLabel {
    private[FormulaLabelDefinitions] inline def apply[N <: Arity](id: String): ConstantConnectorLabel[N] = ConstantConnectorLabel(id, constValue[N])
  }
  object SchematicConnectorLabel {
    inline def apply[N <: Arity](id: String): SchematicConnectorLabel[N] = SchematicConnectorLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): SchematicConnectorLabel[?] = SchematicConnectorLabel(id, arity)
  }

  val neg: ConstantConnectorLabel[1] = ConstantConnectorLabel("¬")
  val implies: ConstantConnectorLabel[2] = ConstantConnectorLabel("⇒")
  val iff: ConstantConnectorLabel[2] = ConstantConnectorLabel("↔")
  val and: ConstantConnectorLabel[2] = ConstantConnectorLabel("∧")
  val or: ConstantConnectorLabel[2] = ConstantConnectorLabel("∨")

  final case class BinderLabel protected(id: String) extends FormulaLabel

  val forall: BinderLabel = BinderLabel("∀")
  val exists: BinderLabel = BinderLabel("∃")
  val existsOne: BinderLabel = BinderLabel("∃!")

}
