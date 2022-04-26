package me.cassayre.florian.masterproject.front.fol.utils

import me.cassayre.florian.masterproject.front.fol.conversions.to.TermConversionsTo
import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions
import me.cassayre.florian.masterproject.front.fol.ops.CommonOps

trait TermUtils {
  this: TermDefinitions & TermConversionsTo & CommonOps =>

  protected abstract class LambdaDefinition[N <: Arity, A <: SchematicLabel & WithArity[?], T <: LabeledTree[?]] {
    val parameters: Seq[A]
    val body: T

    val arity: N = parameters.size.asInstanceOf[N]

    require(parameters.forall(_.arity == 0))
    require(parameters.distinct.size == parameters.size)
  }
  protected abstract class InstantiatedSchema[S <: SchematicLabel & WithArity[?], T <: LabeledTree[_ >: S], A <: SchematicLabel & WithArity[?]] {
    val schema: S
    val lambda: LambdaDefinition[?, A, T]

    require(schema.arity == lambda.arity)
  }


  case class LambdaFunction[N <: Arity] private(parameters: Seq[SchematicFunctionLabel[0]], body: Term) extends LambdaDefinition[N, SchematicFunctionLabel[0], Term]
  object LambdaFunction {
    def apply[N <: Arity](f: FillArgs[SchematicFunctionLabel[0], N] => Term)(using v: ValueOf[N]): LambdaFunction[N] = {
      val n = v.value
      val dummyVariable = SchematicFunctionLabel[0]("") // Used to identify the existing free variables, doesn't matter if this name collides
      val taken = schematicFunctionsOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicFunctionLabel.apply[0](_), n, f, taken)
      new LambdaFunction(params.toSeq, body)
    }
    def unsafe(parameters: Seq[SchematicFunctionLabel[0]], body: Term): LambdaFunction[?] = new LambdaFunction(parameters, body)
  }

  case class InstantiatedFunction private(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?])
    extends InstantiatedSchema[SchematicFunctionLabel[?], Term, SchematicFunctionLabel[0]]
  object InstantiatedFunction {
    def apply[N <: Arity](schema: SchematicFunctionLabel[N], lambda: LambdaFunction[N])(using v: ValueOf[N]): InstantiatedFunction = new InstantiatedFunction(schema, lambda)
    def unsafe(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?]): InstantiatedFunction = new InstantiatedFunction(schema, lambda)
  }


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
    case FunctionTerm(label, args) => FunctionTerm.unsafe(label, args.map(substituteVariables(_, map)))
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
            FunctionTerm.unsafe(label, newArgs)
        }
    }
  }

  def instantiateFunctionSchemas(term: Term, map: Map[SchematicFunctionLabel[?], (Term, Seq[VariableLabel])]): Term = {
    require(map.forall { case (f, (_, args)) => f.arity == args.size })
    instantiateFunctionSchemasInternal(term, map)
  }

  def renameSchemas(
    term: Term,
    functionsMap: Map[SchematicFunctionLabel[?], FunctionLabel[?]],
    variablesMap: Map[VariableLabel, VariableLabel],
    termsMap: Map[SchematicFunctionLabel[0], Term],
  ): Term = term match {
    case VariableTerm(label) =>
      val newLabel = variablesMap.getOrElse(label, label)
      VariableTerm(newLabel)
    case FunctionTerm(label, args) =>
      val result = label match {
        case schema: SchematicFunctionLabel[?] =>
          if(schema.arity == 0) {
            val schema0 = schema.asInstanceOf[SchematicFunctionLabel[0]]
            termsMap.get(schema0).map(Right.apply).getOrElse(Left(functionsMap.getOrElse(schema, label)))
          } else {
            Left(functionsMap.getOrElse(schema, label))
          }
        case _ => Left(label)
      }
      result match {
        case Left(newLabel) => FunctionTerm.unsafe(newLabel, args.map(renameSchemas(_, functionsMap, variablesMap, termsMap)))
        case Right(newTerm) => newTerm
      }
  }

  def fillTupleParametersFunction[N <: Arity](n: N, f: FillArgs[VariableLabel, N] => Term): (FillArgs[VariableLabel, N], Term) = {
    val dummyVariable = VariableLabel("") // Used to identify the existing free variables, doesn't matter if this name collides
    val taken = freeVariablesOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
    fillTupleParameters(VariableLabel.apply, n, f, taken)
  }

}
