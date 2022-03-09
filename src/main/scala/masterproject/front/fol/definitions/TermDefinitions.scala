package masterproject.front.fol.definitions

trait TermDefinitions extends TermLabelDefinitions {

  trait TreeWithLabel[A <: Label] {
    val label: A

    def freeVariables: Set[VariableLabel]
    def functions: Set[FunctionLabel[?]]
  }

  sealed abstract class Term extends TreeWithLabel[TermLabel]

  final case class VariableTerm(label: VariableLabel) extends Term {
    override def freeVariables: Set[VariableLabel] = Set(label)
    override def functions: Set[FunctionLabel[?]] = Set.empty
  }

  final case class FunctionTerm[N <: Int & Singleton](label: FunctionLabel[N], args: Seq[Term]) extends Term {
    require(label.arity == -1 || label.arity == args.size)

    override def freeVariables: Set[VariableLabel] = args.flatMap(_.freeVariables).toSet
    override def functions: Set[FunctionLabel[?]] = args.flatMap(_.functions).toSet

    val arity: Int = label.arity
  }
  object FunctionTerm {
    def unsafe(label: FunctionLabel[?], args: Seq[Term]): FunctionTerm[?] = FunctionTerm(label, args)
  }

}
