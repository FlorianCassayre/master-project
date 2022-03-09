package masterproject.front.fol.definitions

trait TermDefinitions extends TermLabelDefinitions {

  trait TreeWithLabel[A <: Label] {
    val label: A
  }

  sealed abstract class Term extends TreeWithLabel[TermLabel]

  final case class VariableTerm(label: VariableLabel) extends Term

  final case class FunctionTerm[N <: Arity](label: FunctionLabel[N], args: Seq[Term]) extends Term {
    require(label.arity == -1 || label.arity == args.size)
    val arity: Int = label.arity
  }
  object FunctionTerm {
    def unsafe(label: FunctionLabel[?], args: Seq[Term]): FunctionTerm[?] = FunctionTerm(label, args)
  }

}
