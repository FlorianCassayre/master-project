package me.cassayre.florian.masterproject.examples

import me.cassayre.florian.masterproject.front.fol.FOL.{*, given}
import me.cassayre.florian.masterproject.front.proof.Proof.{*, given}
import me.cassayre.florian.masterproject.front.printer.FrontPositionedPrinter.*

@main def frontMatching(): Unit = {
  val (s, t) = (SchematicFunctionLabel[0]("s"), SchematicFunctionLabel[0]("t"))
  val (cs, ct, cu) = (ConstantFunctionLabel[0]("s"), ConstantFunctionLabel[0]("t"), ConstantFunctionLabel[0]("u"))
  val (a, b, c) = (SchematicPredicateLabel[0]("a"), SchematicPredicateLabel[0]("b"), SchematicPredicateLabel[0]("c"))
  val (ca, cb, cc) = (ConstantPredicateLabel[0]("a"), ConstantPredicateLabel[0]("b"), ConstantPredicateLabel[0]("c"))
  val f = SchematicConnectorLabel[1]("f")
  val p = SchematicPredicateLabel[1]("p")
  val cq = ConstantPredicateLabel[1]("q")
  val (x, y, z) = (VariableLabel("x"), VariableLabel("y"), VariableLabel("z"))

  def contextsEqual(ctx1: UnificationContext, ctx2: UnificationContext): Boolean = {
    def names(lambda: WithArityType[?]): Seq[String] = (0 until lambda.arity).map(i => s"unique_name_$i")
    def normalizeFunction(lambda: LambdaFunction[?]): LambdaFunction[?] = {
      val newParams = names(lambda).map(SchematicFunctionLabel.apply[0])
      LambdaFunction.unsafe(
        newParams,
        instantiateTermSchemas(lambda.body, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment })
      )
    }
    def normalizePredicate(lambda: LambdaPredicate[?]): LambdaPredicate[?] = {
      val newParams = names(lambda).map(SchematicFunctionLabel.apply[0])
      LambdaPredicate.unsafe(
        newParams,
        instantiateFormulaSchemas(lambda.body, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment }, Seq.empty, Seq.empty)
      )
    }
    def normalizeConnector(lambda: LambdaConnector[?]): LambdaConnector[?] = {
      val newParams = names(lambda).map(SchematicPredicateLabel.apply[0])
      LambdaConnector.unsafe(
        newParams,
        instantiateFormulaSchemas(lambda.body, Seq.empty, lambda.parameters.zip(newParams).map { case (l1, l2) => RenamedLabel.unsafe(l1, l2).toAssignment }, Seq.empty)
      )
    }
    def normalizeContext(ctx: UnificationContext): UnificationContext =
      UnificationContext(
        ctx.predicates.view.mapValues(normalizePredicate).toMap,
        ctx.functions.view.mapValues(normalizeFunction).toMap,
        ctx.connectors.view.mapValues(normalizeConnector).toMap,
        ctx.variables,
      )
    normalizeContext(ctx1) == normalizeContext(ctx2)
  }

  val sep = ", "
  def prettyContext(ctx: UnificationContext): String = {
    def schema(label: SchematicLabelType): String = s"?${label.id}"
    def assignment(variable: String, value: String): String = s"$variable |-> $value"
    def lambda(parameters: Seq[SchematicLabelType], body: String): String =
      if(parameters.isEmpty) body else s"(${parameters.map(schema).mkString(sep)}) |=> $body"
    "{" +
      (ctx.connectors.toSeq.map { case (k, v) => assignment(schema(k), lambda(v.parameters, prettyFormula(v.body))) } ++
        ctx.predicates.toSeq.map { case (k, v) => assignment(schema(k), lambda(v.parameters, prettyFormula(v.body))) } ++
        ctx.functions.toSeq.map { case (k, v) => assignment(schema(k), lambda(v.parameters, prettyTerm(v.body))) } ++
        ctx.variables.toSeq.map { case (k, v) => assignment(k.id, v.id) }
        ).mkString(sep) +
      "}"
  }

  extension (left: Option[UnificationContext]) {
    infix def ==?==(right: Option[UnificationContext]): Unit = {
      (left, right) match {
        case (Some(l), Some(r)) if !contextsEqual(l, r) =>
          throw AssertionError(s"Expected ${prettyContext(r)}, got ${prettyContext(l)}")
        case (Some(l), None) =>
          throw AssertionError(s"Expected a failure, got ${prettyContext(l)}")
        case (None, Some(r)) =>
          throw AssertionError(s"Expected ${prettyContext(r)}, got a failure")
        case (None, None) =>
          println("Result: (failure)")
        case (Some(l), _) =>
          println(s"Result: ${prettyContext(l)}")
      }
      println()
    }
  }

  var index = 1
  def matching(patterns: PartialSequent*)(values: Sequent*)(ctx: UnificationContext = UnificationContext()): Option[UnificationContext] = {
    println(s"#$index")
    index += 1
    println(s"Patterns: ${patterns.map(prettyPartialSequent(_)).mkString(sep)}  |  Values: ${values.map(prettySequent(_)).mkString(sep)}  |  Partial assignment: ${prettyContext(ctx)}")
    val (patternsISeq, valuesISeq) = (patterns.toIndexedSeq, values.toIndexedSeq)

    unifyAndResolve(
      patternsISeq,
      valuesISeq,
      IndexedSeq.empty,
      ctx,
      matchIndices(Map.empty, patternsISeq, valuesISeq).head,
    ).map(_._2)
  }

  val U = UnificationContext()
  val A = Assigned

  matching(||- (a /\ cb))(|- (cc /\ cb))() ==?== Some(U + A(a, cc))
  matching(||- (a /\ b))(|- (ca /\ cb))(U + A(a, cb)) ==?== None
  matching(||- (a))(|- (cc /\ cb))(U + A(a, cb /\ cc)) ==?== Some(U + A(a, cb /\ cc))
  matching(||- (a))(|- (a /\ cb))() ==?== Some(U + A(a, a /\ cb))
  matching(||- (a /\ a))(|- ((cb \/ cc) /\ (cc \/ cb)))() ==?== Some(U + A(a, cb \/ cc))
  matching(||- (p(ct)))(|- (ct === cu))() ==?== Some(U + A(p, LambdaPredicate[1](x => x === cu)))
  matching(||- (p(t)))(|- (ct === cu))() ==?== None
  matching(||- (p(t)))(|- (ct === cu))(U + A(t, ct)) ==?== Some(U + A(p, LambdaPredicate[1](x => x === cu)) + A(t, ct))
  matching(||- (p(t)))(|- (ct === cu))(U + A(p, LambdaPredicate[1](x => x === cu))) ==?== Some(U + A(p, LambdaPredicate[1](x => x === cu)) + A(t, ct))
  matching(||- (p(t), cq(t)))(|- (ct === cu, cq(ct)))() ==?== Some(U + A(p, LambdaPredicate[1](x => x === cu)) + A(t, ct))
  matching(||- (f(a /\ cb)))(|- ((a /\ b) \/ (b /\ a)))() ==?== None
  matching(||- (f(a /\ cb), a))(|- (cc \/ (cb /\ ca), ca))() ==?== Some(U + A(a, ca) + A(f, LambdaConnector[1](x => cc \/ x)))
  matching(||- (exists(x, cq(x))))(|- (exists(y, cq(y))))() ==?== Some(U + (x, y))
  matching(||- (exists(x, a)))(|- (exists(y, y === cu)))() ==?== None
  matching(||- (exists(x, p(x))))(|- (exists(y, y === cu)))() ==?== Some(U + (x, y) + A(p, LambdaPredicate[1](x => x === cu)))

}
