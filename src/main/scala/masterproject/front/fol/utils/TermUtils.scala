package masterproject.front.fol.utils

import masterproject.front.fol.conversions.TermConversions
import masterproject.front.fol.definitions.TermDefinitions

trait TermUtils {
  this: TermDefinitions & TermConversions =>

  def isSame(t1: Term, t2: Term): Boolean =
    lisa.kernel.fol.FOL.isSame(t1, t2)

  def freeVariablesOf(term: Term): Set[VariableLabel] = term match {
    case VariableTerm(label) => Set(label)
    case FunctionTerm(label, args) => args.flatMap(freeVariablesOf).toSet
  }

  def functionsOf(term: Term): Set[FunctionLabel[?]] = term match {
    case VariableTerm(_) => Set.empty
    case FunctionTerm(label, args) => args.flatMap(functionsOf).toSet + label
  }


  protected case class Scope(boundVariables: Set[VariableLabel] = Set.empty)

  protected def isTermWellFormed(term: Term)(implicit ctx: Scope): Boolean = term match {
    case VariableTerm(label) => ctx.boundVariables.contains(label) // Free variables are prohibited, use schemas
    case FunctionTerm(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isTermWellFormed)
  }

  def isWellFormed(term: Term): Boolean = isTermWellFormed(term)(Scope())


  def substituteVariables(term: Term, map: Map[VariableLabel, Term]): Term = term match {
    case VariableTerm(label) => map.getOrElse(label, term)
    case FunctionTerm(label, args) => FunctionTerm(label, args.map(substituteVariables(_, map)))
  }

  protected def instantiateFunctionSchemasInternal(term: Term, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Term = {
    term match {
      case VariableTerm(label) => term
      case FunctionTerm(label, args) =>
        val option = label match {
          case schematic: SchematicFunctionLabel[?] => map.get(schematic)
          case _ => None
        }
        val newArgs = args.map(instantiateFunctionSchemasInternal(_, map))
        option match {
          case Some((r, args)) =>
            substituteVariables(r, args.zip(newArgs).toMap)
          case None =>
            FunctionTerm(label, newArgs)
        }
    }
  }

  private def instantiateFunctionSchemas(term: Term, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Term = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateFunctionSchemasInternal(term, map)
  }

}
