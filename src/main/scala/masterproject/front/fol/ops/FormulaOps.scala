package masterproject.front.fol.ops

import masterproject.front.fol.definitions.FormulaDefinitions

trait FormulaOps extends CommonOps {
  this: FormulaDefinitions =>

  extension[N <: Arity] (label: PredicateLabel[N])
    def apply: FillTuple[Term, N] => PredicateFormula[N] = args => PredicateFormula(label, tuple2seq(args))

  extension[N <: Arity] (label: ConnectorLabel[N])
    def apply: FillTuple[Formula, N] => ConnectorFormula[N] = args => ConnectorFormula(label, tuple2seq(args))

  extension[N <: Arity] (label: BinderLabel)
    def apply(bound: VariableLabel, inner: Formula): BinderFormula = BinderFormula(label, bound, inner)

  given Conversion[PredicateLabel[0], PredicateFormula[0]] = PredicateFormula(_, Seq.empty)

  given Conversion[ConnectorLabel[0], ConnectorFormula[0]] = ConnectorFormula(_, Seq.empty) // For completeness

  given Conversion[Formula, FormulaLabel] = _.label

  extension (f: Formula) {
    def unary_! : ConnectorFormula[1] = ConnectorFormula(neg, Seq(f))
    infix def ==>(g: Formula): ConnectorFormula[2] = ConnectorFormula(implies, Seq(f, g))
    infix def <=>(g: Formula): ConnectorFormula[2] = ConnectorFormula(iff, Seq(f, g))
    infix def /\(g: Formula): ConnectorFormula[2] = ConnectorFormula(and, Seq(f, g))
    infix def \/(g: Formula): ConnectorFormula[2] = ConnectorFormula(or, Seq(f, g))
  }

  extension (t: Term) {
    infix def ===(u: Term): PredicateFormula[2] = PredicateFormula(equality, Seq(t, u))
  }

  // Extractors

  object ! {
    def unapply(f: Formula): Option[Formula] = f match {
      case ConnectorFormula(`neg`, Seq(g)) => Some(g)
      case _ => None
    }
  }

  sealed abstract class UnapplyBinaryConnector(label: ConnectorLabel[2]) {
    def unapply(f: Formula): Option[(Formula, Formula)] = f match {
      case ConnectorFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object ==> extends UnapplyBinaryConnector(implies)

  object <=> extends UnapplyBinaryConnector(iff)

  object /\ extends UnapplyBinaryConnector(and)

  object \/ extends UnapplyBinaryConnector(or)

  sealed abstract class UnapplyBinaryPredicate(label: PredicateLabel[2]) {
    def unapply(f: Formula): Option[(Term, Term)] = f match {
      case PredicateFormula(`label`, Seq(a, b)) => Some((a, b))
      case _ => None
    }
  }

  object === extends UnapplyBinaryPredicate(equality)

}
