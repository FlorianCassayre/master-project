package me.cassayre.florian.masterproject.front.fol.definitions

trait FormulaLabelDefinitions extends CommonDefinitions {

  sealed abstract class FormulaLabel extends Label

  sealed abstract class PredicateLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  final case class ConstantPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N]
  final case class SchematicPredicateLabel[N <: Arity] protected(id: String, arity: N) extends PredicateLabel[N] with SchematicLabel

  object ConstantPredicateLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantPredicateLabel[N] = ConstantPredicateLabel(id, v.value)
    def unsafe(id: String, arity: Int): ConstantPredicateLabel[?] = ConstantPredicateLabel(id, arity)
  }
  object SchematicPredicateLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicPredicateLabel[N] = SchematicPredicateLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicPredicateLabel[?] = SchematicPredicateLabel(id, arity)
  }

  val equality: ConstantPredicateLabel[2] = ConstantPredicateLabel("=")

  sealed abstract class ConnectorLabel[N <: Arity] extends FormulaLabel with WithArity[N]
  final case class ConstantConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N]
  final case class SchematicConnectorLabel[N <: Arity] protected(id: String, arity: N) extends ConnectorLabel[N] with SchematicLabel

  object ConstantConnectorLabel {
    private[FormulaLabelDefinitions] def apply[N <: Arity](id: String)(using v: ValueOf[N]): ConstantConnectorLabel[N] = ConstantConnectorLabel(id, v.value)
  }
  object SchematicConnectorLabel {
    def apply[N <: Arity](id: String)(using v: ValueOf[N]): SchematicConnectorLabel[N] = SchematicConnectorLabel(id, v.value)
    def unsafe(id: String, arity: Int): SchematicConnectorLabel[?] = SchematicConnectorLabel(id, arity)
  }

  val neg: ConstantConnectorLabel[1] = ConstantConnectorLabel("¬")
  val implies: ConstantConnectorLabel[2] = ConstantConnectorLabel("⇒")
  val iff: ConstantConnectorLabel[2] = ConstantConnectorLabel("↔")
  val and: ConstantConnectorLabel[2] = ConstantConnectorLabel("∧")
  val or: ConstantConnectorLabel[2] = ConstantConnectorLabel("∨")

  final case class BinderLabel private[FormulaLabelDefinitions](id: String) extends FormulaLabel

  val forall: BinderLabel = BinderLabel("∀")
  val exists: BinderLabel = BinderLabel("∃")
  val existsOne: BinderLabel = BinderLabel("∃!")

}
