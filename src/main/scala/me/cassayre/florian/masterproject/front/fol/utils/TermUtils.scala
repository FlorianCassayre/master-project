package me.cassayre.florian.masterproject.front.fol.utils

import me.cassayre.florian.masterproject.front.fol.conversions.to.TermConversionsTo
import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions
import me.cassayre.florian.masterproject.front.fol.ops.CommonOps

trait TermUtils {
  this: TermDefinitions & TermConversionsTo & CommonOps =>

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

  def schematicFunctionsOf(term: Term): Set[SchematicFunctionLabel[?]] =
    functionsOf(term).collect { case schematic: SchematicFunctionLabel[?] => schematic }

  protected case class Scope(boundVariables: Set[VariableLabel] = Set.empty)

  def isWellFormed(term: Term): Boolean = term match {
    case VariableTerm(label) => true
    case FunctionTerm(label, args) =>
      (label.arity == -1 || label.arity == args.size) && args.forall(isWellFormed)
  }


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

  def instantiateFunctionSchemas(term: Term, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Term = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateFunctionSchemasInternal(term, map)
  }

  def renameSchemas(
    term: Term,
    functionsMap: Map[SchematicFunctionLabel[?], SchematicFunctionLabel[?]],
    variablesMap: Map[VariableLabel, VariableLabel],
  ): Term = term match {
    case VariableTerm(label) =>
      val newLabel = variablesMap.getOrElse(label, label)
      VariableTerm(newLabel)
    case FunctionTerm(label, args) =>
      val newLabel = label match {
        case schema: SchematicFunctionLabel[?] if functionsMap.contains(schema) => functionsMap(schema)
        case _ => label
      }
      FunctionTerm(newLabel, args.map(renameSchemas(_, functionsMap, variablesMap)))
  }

  def fillTupleParametersFunction[N <: Arity](n: N, f: FillArgs[VariableLabel, N] => Term): (FillArgs[VariableLabel, N], Term) = {
    val dummyVariable = VariableLabel("") // Used to identify the existing free variables, doesn't matter if this name collides
    val taken = freeVariablesOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
    fillTupleParameters(VariableLabel.apply, n, f, taken)
  }

}
