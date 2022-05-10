package me.cassayre.florian.masterproject.front.fol.utils

import me.cassayre.florian.masterproject.front.fol.conversions.to.TermConversionsTo
import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions
import me.cassayre.florian.masterproject.front.fol.ops.CommonOps

import scala.annotation.targetName

trait TermUtils extends TermDefinitions with TermConversionsTo with CommonOps with CommonUtils {

  type RenamedFunction[B <: FunctionLabel[?]] = RenamedLabel[FunctionLabel[?], SchematicFunctionLabel[?], B]
  type RenamedFunctionSchema = RenamedFunction[SchematicFunctionLabel[?]]

  extension [L <: FunctionLabel[?]](renamed: RenamedFunction[L])
    def toAssignment: AssignedFunction = {
      val parameters = freshIds(Set.empty, renamed.from.arity).map(SchematicFunctionLabel.apply[0])
      AssignedFunction.unsafe(renamed.from, LambdaFunction.unsafe(parameters, FunctionTerm.unsafe(renamed.to, parameters.map(FunctionTerm.unsafe(_, Seq.empty)))))
    }

  def toKernel(lambda: LambdaFunction[?]): lisa.kernel.fol.FOL.LambdaTermTerm =
    lisa.kernel.fol.FOL.LambdaTermTerm(lambda.parameters.map(toKernel), lambda.body)
  given Conversion[LambdaFunction[?], lisa.kernel.fol.FOL.LambdaTermTerm] = toKernel


  case class LambdaFunction[N <: Arity] private(parameters: Seq[SchematicFunctionLabel[0]], body: Term) extends LambdaDefinition[N, SchematicFunctionLabel[0], Term] {
    override type U = Term
    override protected def instantiate(args: Seq[Term]): Term =
      instantiateTermSchemas(body, parameters.zip(args).map { case (from, to) => AssignedFunction(from, LambdaFunction(_ => to)) })
  }
  object LambdaFunction {
    def apply[N <: Arity](f: FillArgs[SchematicFunctionLabel[0], N] => Term)(using v: ValueOf[N]): LambdaFunction[N] = {
      val n = v.value
      val dummyVariable = SchematicFunctionLabel[0]("") // Used to identify the existing free variables, doesn't matter if this name collides
      val taken = schematicFunctionsOf(fillTupleParameters(_ => dummyVariable, n, f)._2).map(_.id)
      val (params, body) = fillTupleParameters(SchematicFunctionLabel.apply[0](_), n, f, taken)
      new LambdaFunction(params.toSeq, body)
    }
    def apply(t: Term): LambdaFunction[0] = LambdaFunction(Seq.empty, t)
    def unsafe(parameters: Seq[SchematicFunctionLabel[0]], body: Term): LambdaFunction[?] = new LambdaFunction(parameters, body)
  }

  case class AssignedFunction private(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?])
    extends AssignedSchema[SchematicFunctionLabel[?], SchematicFunctionLabel[0]] {
    override type L = LambdaFunction[?]
  }
  object AssignedFunction {
    def apply[N <: Arity](schema: SchematicFunctionLabel[N], lambda: LambdaFunction[N])(using v: ValueOf[N]): AssignedFunction = new AssignedFunction(schema, lambda)
    def unsafe(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?]): AssignedFunction = new AssignedFunction(schema, lambda)
  }

  given Conversion[Term, LambdaFunction[0]] = LambdaFunction.apply
  given labelToLambdaFunction[T](using Conversion[T, Term]): Conversion[T, LambdaFunction[0]] = LambdaFunction.apply
  given lambdaToLambdaFunction1: Conversion[SchematicFunctionLabel[0] => Term, LambdaFunction[1]] = LambdaFunction.apply
  given lambdaToLambdaFunction2: Conversion[((SchematicFunctionLabel[0], SchematicFunctionLabel[0])) => Term, LambdaFunction[2]] = LambdaFunction.apply

  /** @see [[lisa.kernel.fol.FOL.isSame]] */
  def isSame(t1: Term, t2: Term): Boolean =
    lisa.kernel.fol.FOL.isSame(t1, t2)

  /** @see [[lisa.kernel.fol.FOL.Term#freeVariables]] */
  def freeVariablesOf(term: Term): Set[VariableLabel] = term match {
    case VariableTerm(label) => Set(label)
    case FunctionTerm(label, args) => args.flatMap(freeVariablesOf).toSet
  }

  def functionsOf(term: Term): Set[FunctionLabel[?]] = term match {
    case VariableTerm(_) => Set.empty
    case FunctionTerm(label, args) => args.flatMap(functionsOf).toSet + label
  }

  /** @see [[lisa.kernel.fol.FOL.Term#schematicFunctions]] */
  def schematicFunctionsOf(term: Term): Set[SchematicFunctionLabel[?]] =
    functionsOf(term).collect { case schematic: SchematicFunctionLabel[?] => schematic }

  protected case class Scope(boundVariables: Set[VariableLabel] = Set.empty)

  /**
   * Checks whether a term is well-formed. Currently returns <code>true</code> at all times.
   * @param term the term to check
   * @return if it is well-formed
   */
  def isWellFormed(term: Term): Boolean = true

  def substituteVariables(term: Term, map: Map[VariableLabel, Term]): Term = term match {
    case VariableTerm(label) => map.getOrElse(label, term)
    case FunctionTerm(label, args) => FunctionTerm.unsafe(label, args.map(substituteVariables(_, map)))
  }

  def instantiateTermSchemas(term: Term, functions: Seq[AssignedFunction]): Term = {
    val map: Map[SchematicFunctionLabel[?], LambdaFunction[?]] = functions.map(i => i.schema -> i.lambda).toMap
    def instantiateInternal(term: Term): Term = term match {
      case _: VariableTerm => term
      case FunctionTerm(label, args) =>
        lazy val newArgs = args.map(instantiateInternal)
        label match {
          case f: SchematicFunctionLabel[?] if map.contains(f) => map(f).unsafe(newArgs)
          case _ => FunctionTerm.unsafe(label, newArgs)
        }
    }
    instantiateInternal(term)
  }

  def unsafeRenameVariables(term: Term, map: Map[VariableLabel, VariableLabel]): Term =
    substituteVariables(term, map.view.mapValues(VariableTerm.apply).toMap)

}
