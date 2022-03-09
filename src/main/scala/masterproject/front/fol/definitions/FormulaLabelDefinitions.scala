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

  final case class ConnectorLabel[N <: Arity] protected(id: String, arity: N) extends FormulaLabel with WithArity[N]

  object ConnectorLabel {
    inline def apply[N <: Arity](id: String): ConnectorLabel[N] = ConnectorLabel(id, constValue[N])
    def unsafe(id: String, arity: Int): ConnectorLabel[?] = ConnectorLabel(id, arity)
  }

  val neg: ConnectorLabel[1] = ConnectorLabel("¬")
  val implies: ConnectorLabel[2] = ConnectorLabel("⇒")
  val iff: ConnectorLabel[2] = ConnectorLabel("↔")
  val and: ConnectorLabel[2] = ConnectorLabel("∧")
  val or: ConnectorLabel[2] = ConnectorLabel("∨")

  final case class BinderLabel protected(id: String) extends FormulaLabel

  val forall: BinderLabel = BinderLabel("∀")
  val exists: BinderLabel = BinderLabel("∃")
  val existsOne: BinderLabel = BinderLabel("∃!")

}
