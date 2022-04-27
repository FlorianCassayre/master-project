package me.cassayre.florian.masterproject.front.fol.utils

import me.cassayre.florian.masterproject.front.fol.conversions.to.TermConversionsTo
import me.cassayre.florian.masterproject.front.fol.definitions.TermDefinitions
import me.cassayre.florian.masterproject.front.fol.ops.CommonOps

import scala.annotation.targetName

trait TermUtils extends TermDefinitions with TermConversionsTo {
  this: CommonOps =>

  def freshId(taken: Set[String], base: String = "x"): String = {
    def findFirst(i: Int): String = {
      val id = s"${base}_$i"
      if(taken.contains(id)) findFirst(i + 1) else id
    }
    findFirst(0)
  }

  def freshIds(taken: Set[String], n: Int, base: String = "x"): Seq[String] = {
    require(n >= 0)
    def findMany(i: Int, n: Int, taken: Set[String], acc: Seq[String]): Seq[String] = {
      if(n > 0) {
        val id = s"${base}_$i"
        if(taken.contains(id)) findMany(i + 1, n, taken, acc) else findMany(i + 1, n - 1, taken + id, id +: acc)
      } else {
        acc
      }
    }
    findMany(0, n, taken, Seq.empty).reverse
  }

  case class RenamedLabel[+B <: Label & WithArity[?], +A <: B & SchematicLabel] private(from: A, to: B)
  object RenamedLabel {
    @targetName("applySafe")
    def apply[N <: Arity, B <: Label & WithArity[N], A <: B & SchematicLabel](from: A, to: B): RenamedLabel[B, A] = new RenamedLabel(from, to)
    def unsafe[B <: Label & WithArity[?], A <: B & SchematicLabel](from: A, to: B): RenamedLabel[B, A] = new RenamedLabel(from, to)
  }
  type RenamedFunction = RenamedLabel[FunctionLabel[?], SchematicFunctionLabel[?]]

  given Conversion[RenamedFunction, AssignedFunction] = s => {
    val parameters = freshIds(Set.empty, s.from.arity).map(SchematicFunctionLabel.apply[0])
    AssignedFunction.unsafe(s.from, LambdaFunction.unsafe(parameters, FunctionTerm.unsafe(s.to, parameters.map(FunctionTerm.unsafe(_, Seq.empty)))))
  }

  protected abstract class LambdaDefinition[N <: Arity, S <: SchematicLabel & WithArity[?], T <: LabeledTree[?]] {
    type U <: LabeledTree[_ >: S]

    val parameters: Seq[S]
    val body: T

    def apply(args: FillArgs[U, N]): T = unsafe(args.toSeq)
    def unsafe(args: Seq[U]): T = {
      require(args.size == arity)
      instantiate(args)
    }
    protected def instantiate(args: Seq[U]): T

    val arity: N = parameters.size.asInstanceOf[N]

    require(parameters.forall(_.arity == 0))
    require(parameters.distinct.size == parameters.size)
  }
  protected abstract class AssignedSchema[R <: SchematicLabel & WithArity[?], S <: SchematicLabel & WithArity[?]] {
    type L <: LambdaDefinition[?, S, _ <: LabeledTree[_ >: R]]

    val schema: R
    val lambda: L

    require(schema.arity == lambda.arity)
  }


  case class LambdaFunction[N <: Arity] private(parameters: Seq[SchematicFunctionLabel[0]], body: Term) extends LambdaDefinition[N, SchematicFunctionLabel[0], Term] {
    override type U = Term
    override protected def instantiate(args: Seq[Term]): Term =
      instantiateSchemas2(body, parameters.zip(args).map { case (from, to) => AssignedFunction(from, LambdaFunction(_ => to)) })
  }
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

  case class AssignedFunction private(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?])
    extends AssignedSchema[SchematicFunctionLabel[?], SchematicFunctionLabel[0]] {
    override type L = LambdaFunction[?]
  }
  object AssignedFunction {
    def apply[N <: Arity](schema: SchematicFunctionLabel[N], lambda: LambdaFunction[N])(using v: ValueOf[N]): AssignedFunction = new AssignedFunction(schema, lambda)
    def unsafe(schema: SchematicFunctionLabel[?], lambda: LambdaFunction[?]): AssignedFunction = new AssignedFunction(schema, lambda)
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

  def instantiateSchemas2(term: Term, substitutions: Seq[AssignedFunction]): Term = {
    val map: Map[SchematicFunctionLabel[?], LambdaFunction[?]] = substitutions.map(i => i.schema -> i.lambda).toMap
    def instantiateInternal(term: Term): Term = term match {
      case _: VariableTerm => term
      case FunctionTerm(label, args) =>
        label match {
          case f: SchematicFunctionLabel[?] if map.contains(f) => map(f).unsafe(args)
          case _ => FunctionTerm.unsafe(label, args.map(instantiateInternal))
        }
    }
    instantiateInternal(term)
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
